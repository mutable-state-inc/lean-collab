//! Mark a goal as decomposed with its children
//!
//! Used by decomposer agents after creating child goals.

use anyhow::Result;
use chrono::Utc;

use crate::config::load_config;
use crate::ensue::EnsueClient;
use crate::goal::{Goal, GoalState};

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

                    // Update state to decomposed
                    goal.state = GoalState::Decomposed {
                        children: children.clone(),
                        strategy: strategy.to_string(),
                        decomposed_at: now,
                    };

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
