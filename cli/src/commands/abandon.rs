//! Manually abandon a goal (for cleanup or error recovery)
//!
//! IMPORTANT: For leaf goals with a parent, this auto-backtracks the parent
//! instead of directly abandoning. This ensures the decomposer can retry
//! with a different strategy.
//!
//! Direct abandon (without parent backtrack) only happens for:
//! - Root goals (no parent)
//! - Goals with --force flag (cleanup/error recovery)

use anyhow::Result;
use chrono::Utc;

use crate::config::load_config;
use crate::ensue::EnsueClient;
use crate::goal::{Goal, GoalState};

/// Minimum tactic attempts required before abandoning a leaf goal
const MIN_ATTEMPTS_FOR_ABANDON: u32 = 6;

pub async fn run(goal_id: &str, reason: Option<&str>, force: bool) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);
    let goal_key = format!("{}/{}", config.goals_prefix(), goal_id);

    let memory = client.get(&goal_key).await?;

    let result = match memory {
        Some(mem) => {
            let goal: Goal = serde_json::from_str(&mem.value)?;
            let now = Utc::now().timestamp();

            // Validation: Check minimum attempt count for leaf goals
            if !force && goal.is_leaf() && goal.attempt_count < MIN_ATTEMPTS_FOR_ABANDON {
                return Ok(println!("{}", serde_json::to_string_pretty(&serde_json::json!({
                    "success": false,
                    "error": "insufficient_attempts",
                    "goal_id": goal_id,
                    "attempt_count": goal.attempt_count,
                    "min_required": MIN_ATTEMPTS_FOR_ABANDON,
                    "message": format!(
                        "Leaf goal requires at least {} tactic attempts before abandoning. Current: {}. Use --force to override.",
                        MIN_ATTEMPTS_FOR_ABANDON,
                        goal.attempt_count
                    ),
                    "suggestion": "Try more tactics with './bin/lc verify' before abandoning",
                }))?));
            }

            // Validation: Check goal state - don't abandon already terminal states
            match &goal.state {
                GoalState::Solved { .. } => {
                    return Ok(println!("{}", serde_json::to_string_pretty(&serde_json::json!({
                        "success": false,
                        "error": "already_solved",
                        "goal_id": goal_id,
                        "message": "Cannot abandon a solved goal",
                    }))?));
                }
                GoalState::Abandoned { .. } => {
                    return Ok(println!("{}", serde_json::to_string_pretty(&serde_json::json!({
                        "success": false,
                        "error": "already_abandoned",
                        "goal_id": goal_id,
                        "message": "Goal is already abandoned",
                    }))?));
                }
                GoalState::Axiom { .. } => {
                    return Ok(println!("{}", serde_json::to_string_pretty(&serde_json::json!({
                        "success": false,
                        "error": "already_axiomatized",
                        "goal_id": goal_id,
                        "message": "Cannot abandon an axiomatized goal",
                    }))?));
                }
                _ => {}
            }

            // AUTO-BACKTRACK: If goal has a parent, backtrack parent instead
            // This ensures the decomposer gets a chance to try a different strategy
            if let Some(parent_id) = &goal.parent {
                if !force {
                    // Delegate to backtrack command on the parent
                    let backtrack_reason = reason.unwrap_or("child_abandon");
                    let full_reason = format!("auto_backtrack:{} - child '{}' abandoned", backtrack_reason, goal_id);

                    // Call backtrack on parent (this will cascade-abandon this goal)
                    return crate::commands::backtrack::run(parent_id, Some(&full_reason)).await;
                }
            }

            // Direct abandon: only for root goals or when --force is used
            let old_state = format!("{:?}", goal.state);

            let mut goal = goal; // Make mutable for update
            goal.state = GoalState::Abandoned {
                parent_backtrack_attempt: 0, // Manual/forced abandon
                abandoned_at: now,
            };

            let goal_json = serde_json::to_string(&goal)?;
            client.update_memory(&goal_key, &goal_json, false).await?;

            serde_json::json!({
                "success": true,
                "goal_id": goal_id,
                "reason": reason.unwrap_or("manual_abandon"),
                "previous_state": old_state,
                "new_state": "abandoned",
                "attempt_count": goal.attempt_count,
                "forced": force,
                "note": if goal.parent.is_some() {
                    "Forced abandon without parent backtrack"
                } else {
                    "Root goal abandoned"
                },
            })
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
