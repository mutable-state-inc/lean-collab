//! Record a goal as axiomatized (agent decides eligibility)

use anyhow::Result;
use chrono::Utc;

use crate::config::load_config;
use crate::ensue::EnsueClient;
use crate::goal::{ClaimOutcome, Goal, GoalState, StrategyAttempt, StrategyCategory, StrategyStatus};

pub async fn run(goal_id: &str, reason: &str) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);
    let goal_key = format!("{}/{}", config.goals_prefix(), goal_id);

    // Fetch goal
    let memory = client.get(&goal_key).await?;

    let result = match memory {
        Some(mem) => {
            let mut goal: Goal = serde_json::from_str(&mem.value)?;
            let now = Utc::now().timestamp();

            // Record strategy attempt
            goal.strategy_attempts.push(StrategyAttempt {
                strategy: format!("axiom: {}", reason),
                category: StrategyCategory::Axiom,
                attempted_at: now,
                duration_ms: None,
                status: StrategyStatus::Succeeded,
                error: None,
                agent: "axiomatize".to_string(),
            });

            // Update state to Axiom
            goal.state = GoalState::Axiom {
                justification: reason.to_string(),
                axiomatized_at: now,
            };

            // Update claim history to mark as axiomatized
            if let Some(last_claim) = goal.claim_history.last_mut() {
                if last_claim.released_at.is_none() {
                    last_claim.released_at = Some(now);
                    last_claim.outcome = Some(ClaimOutcome::Axiomatized);
                }
            }

            // Save updated goal
            let goal_json = serde_json::to_string(&goal)?;
            client.update_memory(&goal_key, &goal_json, false).await?;

            serde_json::json!({
                "success": true,
                "goal_id": goal_id,
                "reason": reason,
                "axiomatized_at": now,
                "new_state": "axiom",
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

    println!("{}", serde_json::to_string(&result)?);
    Ok(())
}
