//! Verify a tactic for a goal using lake env lean
//!
//! On success, records to collective intelligence:
//! - tactics/solutions/{goal_hash} for semantic search

use anyhow::{Context, Result};
use chrono::Utc;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::process::Command;

use crate::config::load_config;
use crate::ensue::{CreateMemoryItem, EmbedSource, EnsueClient};
use crate::goal::{Goal, GoalState, StrategyAttempt, StrategyCategory, StrategyStatus};

/// Hash a goal type for strategy lookup
fn hash_goal_type(goal_type: &str) -> String {
    let mut hasher = DefaultHasher::new();
    goal_type.hash(&mut hasher);
    format!("{:x}", hasher.finish())
}

/// Generate a proper Lean verification file with imports and context
fn generate_lean_code(goal_id: &str, goal: &Goal, tactic: &str, imports: &[String]) -> String {
    let mut code = String::new();

    // Use provided imports, or default to Mathlib.Tactic
    if imports.is_empty() {
        code.push_str("import Mathlib.Tactic\n\n");
    } else {
        for imp in imports {
            code.push_str(&format!("import {}\n", imp));
        }
        code.push('\n');
    }

    // Build the example signature with hypotheses
    if goal.hypotheses.is_empty() {
        // No context - simple example
        code.push_str(&format!(
            "example : {} := by\n  {}\n",
            goal.goal_type, tactic
        ));
    } else {
        // Has hypotheses - include them in the signature
        // Format: example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : goal := by
        let hyp_str = goal.hypotheses
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

            // Create temp lean file in workspace
            let proof_dir = config.workspace.join("proofs");
            std::fs::create_dir_all(&proof_dir)?;
            let proof_file = proof_dir.join(format!("{}.lean", goal_id));

            // Generate proper Lean code with imports and hypotheses
            let lean_code = generate_lean_code(goal_id, &goal, tactic, &imports);

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

            let success = output.status.success();
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            // Record strategy attempt
            goal.strategy_attempts.push(StrategyAttempt {
                strategy: tactic.to_string(),
                category: StrategyCategory::Tactic,
                attempted_at: now,
                duration_ms: None,
                status: if success { StrategyStatus::Succeeded } else { StrategyStatus::Failed },
                error: if success { None } else { Some(stderr.to_string()) },
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
                serde_json::json!({
                    "success": true,
                    "goal_id": goal_id,
                    "tactic": tactic,
                    "verified": false,
                    "error": stderr.to_string(),
                    "stdout": stdout.to_string(),
                    "attempt_count": goal.attempt_count,
                })
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
