//! Undo failed decomposition, mark children abandoned, reopen goal
//!
//! Records failure both locally (goal.strategy_attempts) and globally
//! (strategies/{hash}/{id}) for collective learning.
//!
//! IMPORTANT: Recursively abandons ALL descendants, not just direct children.

use anyhow::Result;
use chrono::Utc;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use crate::config::load_config;
use crate::ensue::{EnsueClient, CreateMemoryItem};
use crate::goal::{Goal, GoalState, StrategyAttempt, StrategyCategory, StrategyStatus};

/// Hash a goal type for strategy lookup
fn hash_goal_type(goal_type: &str) -> String {
    let mut hasher = DefaultHasher::new();
    goal_type.hash(&mut hasher);
    format!("{:x}", hasher.finish())
}

/// Abandon a single goal (non-recursive - just marks direct children)
async fn abandon_goal(
    client: &EnsueClient,
    goals_prefix: &str,
    goal_id: &str,
    backtrack_attempt: u32,
    now: i64,
) -> Result<bool> {
    let goal_key = format!("{}/{}", goals_prefix, goal_id);

    if let Ok(Some(mem)) = client.get(&goal_key).await {
        if let Ok(mut goal) = serde_json::from_str::<Goal>(&mem.value) {
            goal.state = GoalState::Abandoned {
                parent_backtrack_attempt: backtrack_attempt,
                abandoned_at: now,
            };
            let goal_json = serde_json::to_string(&goal)?;
            client.update_memory(&goal_key, &goal_json, false).await?;
            return Ok(true);
        }
    }
    Ok(false)
}

pub async fn run(goal_id: &str, reason: Option<&str>) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);
    let goal_key = format!("{}/{}", config.goals_prefix(), goal_id);

    // Fetch goal
    let memory = client.get(&goal_key).await?;

    let result = match memory {
        Some(mem) => {
            let mut goal: Goal = serde_json::from_str(&mem.value)?;
            let now = Utc::now().timestamp();

            // Must be in Decomposed state to backtrack
            let current_state = goal.state.clone();
            match current_state {
                GoalState::Decomposed { children, strategy, .. } => {
                    let reason_str = reason.unwrap_or("decomposition failed");
                    let goal_hash = hash_goal_type(&goal.goal_type);

                    // 1. Abandon direct children (not recursive - orchestrator handles re-decomposition)
                    let mut abandoned_descendants = Vec::new();
                    for child_id in &children {
                        if abandon_goal(
                            &client,
                            &config.goals_prefix(),
                            child_id,
                            goal.backtrack_count + 1,
                            now,
                        ).await? {
                            abandoned_descendants.push(child_id.clone());
                        }
                    }

                    // 2. Record failed strategy locally in goal
                    goal.strategy_attempts.push(StrategyAttempt {
                        strategy: strategy.clone(),
                        category: StrategyCategory::Decomposition,
                        attempted_at: now,
                        duration_ms: None,
                        status: StrategyStatus::Failed,
                        error: Some(reason_str.to_string()),
                        agent: "backtrack".to_string(),
                    });

                    // 3. Record failed strategy globally for collective learning
                    let strategy_key = format!(
                        "strategies/{}/{}-{}",
                        goal_hash,
                        strategy.replace(" ", "-").replace("/", "-"),
                        now
                    );
                    let strategy_record = serde_json::json!({
                        "goal_type": goal.goal_type,
                        "goal_hash": goal_hash,
                        "strategy": strategy,
                        "category": "decomposition",
                        "status": "failed",
                        "error": reason_str,
                        "goal_id": goal_id,
                        "children_count": children.len(),
                        "backtrack_attempt": goal.backtrack_count + 1,
                        "recorded_at": now,
                    });

                    client.create_memory(&[CreateMemoryItem {
                        key_name: strategy_key.clone(),
                        description: format!(
                            "Failed decomposition strategy '{}' for goal type: {}",
                            strategy, goal.goal_type
                        ),
                        value: serde_json::to_string(&strategy_record)?,
                        embed: Some(true), // Enable semantic search
                        embed_source: None,
                    }]).await?;

                    // 4. Increment backtrack count and update state
                    goal.backtrack_count += 1;
                    goal.state = GoalState::Backtracked {
                        attempt: goal.backtrack_count,
                        backtracked_at: now,
                    };

                    // Save updated goal
                    let goal_json = serde_json::to_string(&goal)?;
                    client.update_memory(&goal_key, &goal_json, false).await?;

                    serde_json::json!({
                        "success": true,
                        "goal_id": goal_id,
                        "reason": reason_str,
                        "backtrack_attempt": goal.backtrack_count,
                        "abandoned_descendants": abandoned_descendants,
                        "abandoned_count": abandoned_descendants.len(),
                        "failed_strategy": strategy,
                        "strategy_key": strategy_key,
                        "new_state": "backtracked",
                    })
                }
                other => {
                    serde_json::json!({
                        "success": false,
                        "error": "invalid_state",
                        "goal_id": goal_id,
                        "current_state": other,
                        "message": "Goal must be in Decomposed state to backtrack",
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
