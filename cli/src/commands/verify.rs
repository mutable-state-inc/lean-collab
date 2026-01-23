//! Verify a tactic for a goal using lake env lean
//!
//! On success, records to collective intelligence:
//! - tactics/solutions/{goal_hash} for semantic search
//!
//! Uses warm server if running for faster verification.

use anyhow::{Context, Result};
use chrono::Utc;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::process::Command;

use crate::config::load_config;
use crate::ensue::{CreateMemoryItem, EmbedSource, EnsueClient};
use crate::goal::{ClaimOutcome, Goal, GoalState, StrategyAttempt, StrategyCategory, StrategyStatus};
use super::warm::{self, VerifyRequest, WarmRequest};

/// Hash a goal type for strategy lookup
fn hash_goal_type(goal_type: &str) -> String {
    let mut hasher = DefaultHasher::new();
    goal_type.hash(&mut hasher);
    format!("{:x}", hasher.finish())
}

/// Generate a proper Lean verification file with imports and context
fn generate_lean_code(goal_id: &str, goal: &Goal, tactic: &str, imports: &[String]) -> String {
    let mut code = String::new();

    // Use provided imports, or default to Mathlib.Tactic plus commonly needed modules
    if imports.is_empty() {
        code.push_str("import Mathlib.Tactic\n");
        code.push_str("import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic\n");
        code.push_str("import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds\n");
        code.push_str("import Mathlib.Analysis.Real.Pi.Bounds\n");
        code.push_str("import Mathlib.Analysis.Calculus.Deriv.Basic\n");
        code.push_str("import Mathlib.Analysis.Convex.Function\n");
        code.push_str("import Mathlib.Analysis.Convex.SpecificFunctions.Deriv\n");
        code.push_str("import Mathlib.Topology.Order.Basic\n\n");
    } else {
        for imp in imports {
            code.push_str(&format!("import {}\n", imp));
        }
        code.push('\n');
    }

    // Build the example signature with hypotheses
    // Filter out empty strings that may have been stored
    let valid_hypotheses: Vec<_> = goal.hypotheses
        .iter()
        .filter(|h| !h.trim().is_empty())
        .collect();

    if valid_hypotheses.is_empty() {
        // No context - simple example
        code.push_str(&format!(
            "example : {} := by\n  {}\n",
            goal.goal_type, tactic
        ));
    } else {
        // Has hypotheses - include them in the signature
        // Format: example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : goal := by
        let hyp_str = valid_hypotheses
            .iter()
            .map(|h| format!("({})", h))
            .collect::<Vec<_>>()
            .join(" ");

        code.push_str(&format!(
            "example {} : {} := by\n  {}\n",
            hyp_str, goal.goal_type, tactic
        ));
    }

    // Add comment header at top
    let header = format!(
        "-- Auto-generated verification for goal: {}\n-- Goal type: {}\n\n",
        goal_id, goal.goal_type
    );

    header + &code
}

pub async fn run(goal_id: &str, tactic: &str, imports: Option<Vec<String>>) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);
    let goal_key = format!("{}/{}", config.goals_prefix(), goal_id);
    let imports = imports.unwrap_or_default();

    // Fetch goal
    let memory = client.get(&goal_key).await?;

    let result = match memory {
        Some(mem) => {
            let mut goal: Goal = serde_json::from_str(&mem.value)?;
            let now = Utc::now().timestamp();

            // Check if warm server is running
            let use_warm = warm::is_server_running();

            let (success, error_msg, stdout_str): (bool, Option<String>, String) = if use_warm {
                // Use warm server for faster verification
                eprintln!("Using warm server for verification...");
                let req = VerifyRequest {
                    goal: goal.goal_type.clone(),
                    hypotheses: goal.hypotheses.clone(),
                    tactic: tactic.to_string(),
                    imports: imports.clone(),
                };

                match warm::send_verify_request(&req) {
                    Ok(resp) => {
                        let tactic_has_sorry = tactic.to_lowercase().contains("sorry");
                        let final_success = resp.success && !tactic_has_sorry;
                        let final_error = if tactic_has_sorry {
                            Some("Tactic contains 'sorry' - this is not a valid proof".to_string())
                        } else {
                            resp.error
                        };
                        (final_success, final_error, resp.stdout.unwrap_or_default())
                    }
                    Err(e) => {
                        eprintln!("Warm server error: {}, falling back to cold run", e);
                        run_cold_verify(&config, goal_id, &goal, tactic, &imports)?
                    }
                }
            } else {
                // Cold run
                run_cold_verify(&config, goal_id, &goal, tactic, &imports)?
            };

            // Record strategy attempt
            goal.strategy_attempts.push(StrategyAttempt {
                strategy: tactic.to_string(),
                category: StrategyCategory::Tactic,
                attempted_at: now,
                duration_ms: None,
                status: if success { StrategyStatus::Succeeded } else { StrategyStatus::Failed },
                error: error_msg.clone(),
                agent: "verify".to_string(),
            });
            goal.attempt_count += 1;

            if success {
                // Update goal state to Solved
                goal.state = GoalState::Solved {
                    tactic: tactic.to_string(),
                    imports: imports.clone(),
                    solved_at: now,
                };

                // Update claim history to mark as solved
                if let Some(last_claim) = goal.claim_history.last_mut() {
                    if last_claim.released_at.is_none() {
                        last_claim.released_at = Some(now);
                        last_claim.outcome = Some(ClaimOutcome::Solved);
                    }
                }

                // Unsubscribe from solved goal
                let _ = client.unsubscribe(&goal_key).await;
            }

            // Save updated goal
            let goal_json = serde_json::to_string(&goal)?;
            client.update_memory(&goal_key, &goal_json, false).await?;

            // Record to collective intelligence
            let goal_hash = hash_goal_type(&goal.goal_type);
            let solution_key = format!("tactics/solutions/{}-{}", goal_hash, now);

            if success {
                // Record successful tactic for semantic search
                let solution_record = serde_json::json!({
                    "goal_type": goal.goal_type,
                    "goal_hash": goal_hash,
                    "tactic": tactic,
                    "status": "succeeded",
                    "goal_id": goal_id,
                    "theorem_id": config.theorem_id,
                    "recorded_at": now,
                });

                client.create_memory(&[CreateMemoryItem {
                    key_name: solution_key.clone(),
                    description: format!("{} := by {}", goal.goal_type, tactic),
                    value: serde_json::to_string(&solution_record)?,
                    embed: Some(true), // Enable semantic search
                    embed_source: Some(EmbedSource::Description), // Embed the goal type + tactic
                }]).await?;

                serde_json::json!({
                    "success": true,
                    "goal_id": goal_id,
                    "tactic": tactic,
                    "verified": true,
                    "new_state": "solved",
                    "solution_key": solution_key,
                })
            } else {
                let error_str = error_msg.clone().unwrap_or_else(|| "Unknown error".to_string());

                // Check if error is "Unknown identifier" - if so, auto-run suggest
                let suggestions = if error_str.contains("unknown identifier") ||
                                     error_str.contains("Unknown identifier") ||
                                     error_str.contains("unknown constant") {
                    // Run suggest to help prover find real lemmas
                    get_suggestions_for_goal(&goal)
                } else {
                    None
                };

                let mut result = serde_json::json!({
                    "success": true,
                    "goal_id": goal_id,
                    "tactic": tactic,
                    "verified": false,
                    "error": error_str,
                    "stdout": stdout_str,
                    "attempt_count": goal.attempt_count,
                    "warm_server": use_warm,
                });

                // Add suggestions if we found any
                if let Some(ref sugg) = suggestions {
                    result["hint"] = serde_json::json!("Unknown lemma. Try these real lemmas from Lean:");
                    result["suggestions"] = serde_json::json!(sugg);
                }

                result
            }
        }
        None => {
            serde_json::json!({
                "success": false,
                "error": "not_found",
                "goal_id": goal_id,
            })
        }
    };

    println!("{}", serde_json::to_string_pretty(&result)?);
    Ok(())
}

/// Run verification without warm server (cold run)
fn run_cold_verify(
    config: &crate::config::LoadedConfig,
    goal_id: &str,
    goal: &Goal,
    tactic: &str,
    imports: &[String],
) -> Result<(bool, Option<String>, String)> {
    // Create temp lean file in workspace
    let proof_dir = config.workspace.join("proofs");
    std::fs::create_dir_all(&proof_dir)?;
    let proof_file = proof_dir.join(format!("{}.lean", goal_id));

    // Generate proper Lean code with imports and hypotheses
    let lean_code = generate_lean_code(goal_id, goal, tactic, imports);

    std::fs::write(&proof_file, &lean_code)
        .with_context(|| format!("Failed to write {}", proof_file.display()))?;

    // Run lake env lean
    let lean_project = config.lean_project_root.as_ref()
        .map(|p| p.as_path())
        .unwrap_or(&config.workspace);

    let output = Command::new("lake")
        .args(["env", "lean", proof_file.to_str().unwrap()])
        .current_dir(lean_project)
        .output()
        .context("Failed to run lake env lean")?;

    let exit_success = output.status.success();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Lean often puts errors in stdout, not stderr
    let stdout_has_error = stdout.contains("error:") || stdout.contains("Error:");
    let lean_success = exit_success && !stdout_has_error;

    // Check for sorry
    let tactic_has_sorry = tactic.to_lowercase().contains("sorry");
    let output_has_sorry = stdout.to_lowercase().contains("sorry")
        || stderr.to_lowercase().contains("sorry")
        || stderr.contains("declaration uses 'sorry'");

    let success = lean_success && !tactic_has_sorry && !output_has_sorry;

    // Build error message
    let error_msg = if tactic_has_sorry {
        Some("Tactic contains 'sorry' - this is not a valid proof".to_string())
    } else if output_has_sorry {
        Some("Proof uses 'sorry' - this is not a valid proof".to_string())
    } else if !stderr.trim().is_empty() {
        Some(stderr.to_string())
    } else if stdout_has_error {
        Some(stdout.to_string())
    } else if !lean_success {
        Some("Unknown Lean error".to_string())
    } else {
        None
    };

    Ok((success, error_msg, format!("{}\n{}", stdout, stderr)))
}

/// Get suggestions for a goal using the warm server or suggest command
fn get_suggestions_for_goal(goal: &Goal) -> Option<Vec<String>> {
    // Try using warm server first
    if warm::is_server_running() {
        let req = WarmRequest {
            goal: goal.goal_type.clone(),
            hypotheses: goal.hypotheses.clone(),
            tactic: "apply?".to_string(),
            imports: vec![
                "Mathlib.Tactic".to_string(),
                "Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds".to_string(),
            ],
        };

        if let Ok(resp) = warm::send_request(&req) {
            if !resp.suggestions.is_empty() {
                return Some(resp.suggestions.iter().map(|s| s.tactic.clone()).collect());
            }
        }
    }

    // Fallback: return None (don't block on cold suggest)
    None
}
