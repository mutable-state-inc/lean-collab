//! Release a claim on a goal (called by hooks on agent exit)

use anyhow::Result;
use chrono::Utc;

use crate::config::load_config;
use crate::ensue::EnsueClient;
use crate::goal::{Goal, GoalState, ClaimOutcome};

pub async fn run(goal_id: &str, agent: Option<&str>) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);

    let agent_id = agent.unwrap_or("unknown");
    let goal_key = format!("{}/{}", config.goals_prefix(), goal_id);

    // Fetch current goal
    let memory = client.get(&goal_key).await?;

    let result = match memory {
        Some(mem) => {
            let mut goal: Goal = serde_json::from_str(&mem.value)?;
            let now = Utc::now().timestamp();

            match &goal.state {
                GoalState::Working { agent: current_agent, .. } => {
                    // Verify ownership (or allow unclaim if agent matches or is "unknown")
                    if current_agent != agent_id && agent_id != "unknown" {
                        return Ok(println!("{}", serde_json::to_string(&serde_json::json!({
                            "success": false,
                            "error": "not_owner",
                            "goal_id": goal_id,
                            "current_agent": current_agent,
                            "requesting_agent": agent_id,
                        }))?));
                    }

                    // Update claim history
                    if let Some(last_claim) = goal.claim_history.last_mut() {
                        last_claim.released_at = Some(now);
                        last_claim.outcome = Some(ClaimOutcome::Released);
                    }

                    // Transition state back to Open
                    goal.state = GoalState::Open;

                    // Update in Ensue
                    let goal_json = serde_json::to_string(&goal)?;
                    client.update_memory(&goal_key, &goal_json, false).await?;

                    serde_json::json!({
                        "success": true,
                        "goal_id": goal_id,
                        "agent": agent_id,
                        "released_at": now,
                        "outcome": "released",
                        "new_state": "open",
                    })
                }
                GoalState::Solved { .. } => {
                    // Already solved - just update claim history
                    if let Some(last_claim) = goal.claim_history.last_mut() {
                        if last_claim.released_at.is_none() {
                            last_claim.released_at = Some(now);
                            last_claim.outcome = Some(ClaimOutcome::Solved);

                            let goal_json = serde_json::to_string(&goal)?;
                            client.update_memory(&goal_key, &goal_json, false).await?;
                        }
                    }

                    serde_json::json!({
                        "success": true,
                        "goal_id": goal_id,
                        "agent": agent_id,
                        "released_at": now,
                        "outcome": "solved",
                        "new_state": "solved",
                    })
                }
                GoalState::Decomposed { .. } => {
                    // Already decomposed - update claim history
                    if let Some(last_claim) = goal.claim_history.last_mut() {
                        if last_claim.released_at.is_none() {
                            last_claim.released_at = Some(now);
                            last_claim.outcome = Some(ClaimOutcome::Decomposed);

                            let goal_json = serde_json::to_string(&goal)?;
                            client.update_memory(&goal_key, &goal_json, false).await?;
                        }
                    }

                    serde_json::json!({
                        "success": true,
                        "goal_id": goal_id,
                        "agent": agent_id,
                        "released_at": now,
                        "outcome": "decomposed",
                        "new_state": "decomposed",
                    })
                }
                GoalState::Axiom { .. } => {
                    // Already axiomatized - update claim history
                    if let Some(last_claim) = goal.claim_history.last_mut() {
                        if last_claim.released_at.is_none() {
                            last_claim.released_at = Some(now);
                            last_claim.outcome = Some(ClaimOutcome::Axiomatized);

                            let goal_json = serde_json::to_string(&goal)?;
                            client.update_memory(&goal_key, &goal_json, false).await?;
                        }
                    }

                    serde_json::json!({
                        "success": true,
                        "goal_id": goal_id,
                        "agent": agent_id,
                        "released_at": now,
                        "outcome": "axiomatized",
                        "new_state": "axiom",
                    })
                }
                other => {
                    serde_json::json!({
                        "success": false,
                        "error": "not_claimed",
                        "goal_id": goal_id,
                        "current_state": other,
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

    println!("{}", serde_json::to_string(&result)?);
    Ok(())
}
