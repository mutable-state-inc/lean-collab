//! Mark a goal as decomposed with its children
//!
//! Used by decomposer agents after creating child goals.
//! Validates that the strategy is valid Lean tactic syntax before storing.

use anyhow::Result;
use chrono::Utc;
use std::process::Command;

use crate::config::{load_config, LoadedConfig};
use crate::ensue::EnsueClient;
use crate::goal::{ClaimOutcome, Goal, GoalState};

/// Validate that a strategy string is valid Lean tactic syntax.
/// Uses a quick Lean check with Mathlib.Tactic import (~2s).
/// Returns Ok(()) if valid, Err with message if invalid.
fn validate_tactic_syntax(strategy: &str, config: &LoadedConfig) -> Result<(), String> {
    // Skip validation for empty strategies
    if strategy.trim().is_empty() {
        return Ok(());
    }

    // Create a minimal Lean file to check if the tactic parses
    // We use `example : True := by <strategy>` which will:
    // - Succeed or fail with type errors if strategy is valid Lean tactic syntax
    // - Fail with "unknown tactic" if strategy is natural language
    // We accept any result that isn't "unknown tactic"
    let lean_code = format!(
        "import Mathlib.Tactic\nexample : True := by {}",
        strategy
    );

    let lean_project = config.lean_project_root.as_ref()
        .map(|p| p.as_path())
        .unwrap_or(&config.workspace);

    let output = Command::new("lake")
        .args(["env", "lean", "--stdin"])
        .current_dir(lean_project)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            use std::io::Write;
            if let Some(stdin) = child.stdin.as_mut() {
                stdin.write_all(lean_code.as_bytes())?;
            }
            child.wait_with_output()
        });

    match output {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            // Check for "unknown tactic" which indicates natural language or invalid tactic
            // Other errors (like type mismatches, "failed") are fine - they just mean
            // the tactic is valid syntax but doesn't apply to our test goal
            if stdout.contains("unknown tactic") || stderr.contains("unknown tactic") {
                return Err(format!(
                    "Strategy '{}' is not valid Lean tactic syntax (unknown tactic)",
                    strategy
                ));
            }

            // If we get here, the tactic is valid Lean syntax (even if it had type errors)
            Ok(())
        }
        Err(e) => {
            // If we can't run Lean, log warning but allow the decomposition
            // This prevents blocking if Lean is unavailable
            eprintln!("Warning: Could not validate tactic syntax: {}", e);
            Ok(())
        }
    }
}

pub async fn run(
    goal_id: &str,
    children: Vec<String>,
    strategy: &str,
) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);

    let goal_key = format!("{}/{}", config.goals_prefix(), goal_id);

    // Fetch current goal
    let memory = client.get(&goal_key).await?;

    let result = match memory {
        Some(mem) => {
            let mut goal: Goal = serde_json::from_str(&mem.value)?;
            let now = Utc::now().timestamp();

            // Verify goal is in a valid state for decomposition
            match &goal.state {
                GoalState::Open | GoalState::Working { .. } | GoalState::Backtracked { .. } => {
                    // Valid states for decomposition

                    // Validate that the strategy is valid Lean tactic syntax
                    if let Err(validation_error) = validate_tactic_syntax(strategy, &config) {
                        return Ok(println!("{}", serde_json::to_string_pretty(&serde_json::json!({
                            "success": false,
                            "error": "invalid_strategy",
                            "goal_id": goal_id,
                            "strategy": strategy,
                            "message": validation_error,
                            "suggestion": "The strategy must be valid Lean tactic syntax, not natural language. Examples: 'intro x hx', 'constructor', 'by_cases h : x ≤ 0'"
                        }))?));
                    }

                    // Update state to decomposed
                    goal.state = GoalState::Decomposed {
                        children: children.clone(),
                        strategy: strategy.to_string(),
                        decomposed_at: now,
                    };

                    // Update claim history to mark as decomposed
                    if let Some(last_claim) = goal.claim_history.last_mut() {
                        if last_claim.released_at.is_none() {
                            last_claim.released_at = Some(now);
                            last_claim.outcome = Some(ClaimOutcome::Decomposed);
                        }
                    }

                    // Unsubscribe from decomposed goal (children are subscribed separately)
                    let _ = client.unsubscribe(&goal_key).await;

                    // Update in Ensue
                    let goal_json = serde_json::to_string(&goal)?;
                    client.update_memory(&goal_key, &goal_json, false).await?;

                    serde_json::json!({
                        "success": true,
                        "goal_id": goal_id,
                        "state": "decomposed",
                        "children": children,
                        "strategy": strategy,
                        "decomposed_at": now,
                    })
                }
                GoalState::Decomposed { children: existing_children, .. } => {
                    serde_json::json!({
                        "success": false,
                        "error": "already_decomposed",
                        "goal_id": goal_id,
                        "existing_children": existing_children,
                    })
                }
                GoalState::Solved { .. } => {
                    serde_json::json!({
                        "success": false,
                        "error": "already_solved",
                        "goal_id": goal_id,
                    })
                }
                other => {
                    serde_json::json!({
                        "success": false,
                        "error": "invalid_state",
                        "goal_id": goal_id,
                        "current_state": format!("{:?}", other),
                    })
                }
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
