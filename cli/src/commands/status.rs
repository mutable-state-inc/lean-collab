//! Query comprehensive goal/theorem metadata

use anyhow::Result;
use std::collections::HashMap;

use crate::config::load_config;
use crate::ensue::EnsueClient;
use crate::goal::{Goal, GoalState};

pub async fn run(goal_id: Option<&str>, _watch: bool) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);

    if let Some(gid) = goal_id {
        // Get specific goal status
        let goal_status = get_goal_status(&client, &config.goals_prefix(), gid, config.max_depth).await?;
        println!("{}", serde_json::to_string_pretty(&goal_status)?);
    } else {
        // Get theorem-level summary
        let summary = get_theorem_summary(&client, &config).await?;
        println!("{}", serde_json::to_string_pretty(&summary)?);
    }

    Ok(())
}

async fn get_goal_status(
    client: &EnsueClient,
    goals_prefix: &str,
    goal_id: &str,
    max_depth: u32,
) -> Result<serde_json::Value> {
    let key = format!("{}/{}", goals_prefix, goal_id);

    let memory = client.get(&key).await?;

    match memory {
        Some(mem) => {
            // Parse the goal
            let goal: Goal = serde_json::from_str(&mem.value)?;

            // Build comprehensive status
            Ok(serde_json::json!({
                "success": true,
                "goal": {
                    "id": goal.id,
                    "goal_type": goal.goal_type,
                    "state": goal.state,
                    "depth": goal.depth,
                    "parent": goal.parent,
                    "is_leaf": goal.is_leaf(),
                    "complexity": goal.complexity(),
                    "can_decompose": goal.can_decompose(max_depth),
                    "hypotheses": goal.hypotheses,
                    // Structural analysis
                    "has_quantifiers": goal.has_quantifiers,
                    "has_transcendentals": goal.has_transcendentals,
                    "is_numeric": goal.is_numeric,
                    // History
                    "attempt_count": goal.attempt_count,
                    "backtrack_count": goal.backtrack_count,
                    "claim_history": goal.claim_history,
                    "strategy_attempts": goal.strategy_attempts,
                    // Metadata
                    "created_at": goal.created_at,
                }
            }))
        }
        None => Ok(serde_json::json!({
            "success": false,
            "error": format!("Goal not found: {}", goal_id)
        })),
    }
}

async fn get_theorem_summary(
    client: &EnsueClient,
    config: &crate::config::LoadedConfig,
) -> Result<serde_json::Value> {
    // List all goals for this theorem (prefix match, no wildcard needed)
    let all_keys = client
        .list_keys(Some(&config.goals_prefix()), 5000, 0)
        .await?;

    // Filter to only goal objects (not sub-keys like /children, /tactic, etc.)
    // Goal keys are exactly: proofs/{tid}/goals/{gid} (no further slashes)
    let prefix = config.goals_prefix();
    let keys: Vec<_> = all_keys
        .into_iter()
        .filter(|k| {
            // Remove prefix and check there's no more slashes
            let suffix = k.key.strip_prefix(&prefix).unwrap_or(&k.key);
            let suffix = suffix.trim_start_matches('/');
            !suffix.contains('/')
        })
        .collect();

    // Fetch all goals
    let key_strs: Vec<&str> = keys.iter().map(|k| k.key.as_str()).collect();

    let mut counters: HashMap<&str, u32> = HashMap::new();
    let mut open_goals = Vec::new();
    let mut working_goals = Vec::new();

    if !key_strs.is_empty() {
        // Batch fetch in chunks of 100
        for chunk in key_strs.chunks(100) {
            let memories = client.get_memory(chunk).await?;

            for (_key, mem) in memories {
                if let Ok(goal) = serde_json::from_str::<Goal>(&mem.value) {
                    let state_name = match &goal.state {
                        GoalState::Open => "open",
                        GoalState::Working { .. } => "working",
                        GoalState::Solved { .. } => "solved",
                        GoalState::Decomposed { .. } => "decomposed",
                        GoalState::Axiom { .. } => "axiomatized",
                        GoalState::Backtracked { .. } => "backtracked",
                        GoalState::Exhausted { .. } => "exhausted",
                        GoalState::Abandoned { .. } => "abandoned",
                    };

                    *counters.entry(state_name).or_insert(0) += 1;

                    match &goal.state {
                        GoalState::Open | GoalState::Backtracked { .. } => {
                            open_goals.push(serde_json::json!({
                                "id": goal.id,
                                "depth": goal.depth,
                                "complexity": goal.complexity(),
                                "can_decompose": goal.can_decompose(config.max_depth),
                                "has_quantifiers": goal.has_quantifiers,
                                "attempt_count": goal.attempt_count,
                            }));
                        }
                        GoalState::Working { agent, expires_at, .. } => {
                            working_goals.push(serde_json::json!({
                                "id": goal.id,
                                "agent": agent,
                                "expires_at": expires_at,
                            }));
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    let total: u32 = counters.values().sum();
    let solved = counters.get("solved").copied().unwrap_or(0);
    let decomposed = counters.get("decomposed").copied().unwrap_or(0);
    let axiomatized = counters.get("axiomatized").copied().unwrap_or(0);
    let open = counters.get("open").copied().unwrap_or(0);
    let working = counters.get("working").copied().unwrap_or(0);
    let backtracked = counters.get("backtracked").copied().unwrap_or(0);
    let exhausted = counters.get("exhausted").copied().unwrap_or(0);

    // Ready to compose when all leaf goals are solved/axiomatized and none need work
    // Must check: open, working, backtracked (needs re-decomposition), exhausted (failed), abandoned (failed)
    // If ANY goal is abandoned, the proof is incomplete - don't report ready to compose
    let abandoned = counters.get("abandoned").copied().unwrap_or(0);
    let ready_to_compose = total > 0 && open == 0 && working == 0 && backtracked == 0 && exhausted == 0 && abandoned == 0;

    // Limit open_goals to available capacity (enforce max_parallel_agents at CLI level)
    let working_count = working_goals.len();
    let available_capacity = (config.max_parallel_agents as usize).saturating_sub(working_count);
    let claimable_goals: Vec<_> = open_goals.into_iter().take(available_capacity).collect();

    // Detect "stuck" state: no work to do, but proof is incomplete
    // This happens when children are abandoned but parent hasn't been backtracked
    let is_stuck = open == 0 && working == 0 && abandoned > 0 && !ready_to_compose;

    Ok(serde_json::json!({
        "success": true,
        "theorem_id": config.theorem_id,
        "summary": {
            "total": total,
            "open": open,
            "working": working,
            "solved": solved,
            "decomposed": decomposed,
            "axiomatized": axiomatized,
            "backtracked": counters.get("backtracked").copied().unwrap_or(0),
            "exhausted": counters.get("exhausted").copied().unwrap_or(0),
            "abandoned": counters.get("abandoned").copied().unwrap_or(0),
        },
        "ready_to_compose": ready_to_compose,
        "is_stuck": is_stuck,
        "stuck_hint": if is_stuck {
            Some("Proof is stuck: goals abandoned but no work available. Backtrack parent goals to try different strategies.")
        } else {
            None
        },
        "open_goals": claimable_goals,
        "open_goals_total": open,
        "available_capacity": available_capacity,
        "working_goals": working_goals,
        "config": {
            "max_parallel_agents": config.max_parallel_agents,
            "max_depth": config.max_depth,
        }
    }))
}
