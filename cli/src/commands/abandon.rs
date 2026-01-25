//! Manually abandon a goal (mark as failed/exhausted)
//!
//! Abandoning a goal does NOT cascade to siblings or backtrack the parent.
//! Each goal is independent - siblings continue working.
//!
//! Parent backtrack should only happen when:
//! - The decomposition strategy is proven wrong (use `./bin/lc backtrack`)
//! - ALL children have failed (orchestrator decides)
//!
//! This prevents wasteful cascade-abandonment of untried siblings.

use anyhow::Result;
use chrono::Utc;

use crate::config::load_config;
use crate::ensue::EnsueClient;
use crate::goal::{Goal, GoalState};

/// Minimum tactic attempts required before abandoning a leaf goal
const MIN_ATTEMPTS_FOR_ABANDON: u32 = 6;

pub async fn run(goal_id: &str, reason: Option<&str>, force: bool) -> Result<()> {
    // DEBUG: Log all abandon calls to a file for debugging
    use std::fs::OpenOptions;
    use std::io::Write;
    if let Ok(mut f) = OpenOptions::new().create(true).append(true).open("/tmp/abandon-debug.log") {
        let _ = writeln!(f, "[{}] ABANDON: goal={}, reason={:?}, force={}",
            chrono::Utc::now().format("%H:%M:%S"), goal_id, reason, force);
    }
    eprintln!("[ABANDON DEBUG] goal_id={}, reason={:?}, force={}", goal_id, reason, force);

    let config = load_config()?;
    let client = EnsueClient::from_config(&config);
    let goal_key = format!("{}/{}", config.goals_prefix(), goal_id);

    let memory = client.get(&goal_key).await?;

    let result = match memory {
        Some(mem) => {
            let goal: Goal = serde_json::from_str(&mem.value)?;
            let now = Utc::now().timestamp();

            // Validation: Check minimum attempt count for leaf goals
            if let Ok(mut f) = OpenOptions::new().create(true).append(true).open("/tmp/abandon-debug.log") {
                let _ = writeln!(f, "  is_leaf={}, attempt_count={}, force={}", goal.is_leaf(), goal.attempt_count, force);
            }
            eprintln!("[ABANDON DEBUG] is_leaf={}, attempt_count={}, force={}", goal.is_leaf(), goal.attempt_count, force);
            if !force && goal.is_leaf() && goal.attempt_count < MIN_ATTEMPTS_FOR_ABANDON {
                if let Ok(mut f) = OpenOptions::new().create(true).append(true).open("/tmp/abandon-debug.log") {
                    let _ = writeln!(f, "  BLOCKED by MIN_ATTEMPTS");
                }
                eprintln!("[ABANDON DEBUG] BLOCKED by MIN_ATTEMPTS check");
                return Ok(println!("{}", serde_json::to_string_pretty(&serde_json::json!({
                    "success": false,
                    "error": "insufficient_attempts",
                    "goal_id": goal_id,
                    "attempt_count": goal.attempt_count,
                    "min_required": MIN_ATTEMPTS_FOR_ABANDON,
                    "message": format!(
                        "Leaf goal requires at least {} tactic attempts before abandoning. Current: {}. Try more tactics first.",
                        MIN_ATTEMPTS_FOR_ABANDON,
                        goal.attempt_count
                    ),
                    "suggestion": "Try more tactics with './bin/lc verify' before abandoning",
                }))?));
            }
            eprintln!("[ABANDON DEBUG] PASSED MIN_ATTEMPTS check (will proceed)");

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

            // SPECIAL CASE: "needs_decomposition" means THIS goal should be decomposed,
            // not backtrack the parent. Release claim and mark for decomposer.
            let reason_str = reason.unwrap_or("");
            if reason_str.contains("needs_decomposition") {
                let mut goal = goal.clone();
                goal.state = GoalState::Open; // Release back to open for decomposer
                // Reset attempt count so decomposer gets fresh start
                // (tactic attempts don't apply to decomposition)

                let goal_json = serde_json::to_string(&goal)?;
                client.update_memory(&goal_key, &goal_json, false).await?;

                return Ok(println!("{}", serde_json::to_string_pretty(&serde_json::json!({
                    "success": true,
                    "goal_id": goal_id,
                    "action": "released_for_decomposition",
                    "reason": reason_str,
                    "new_state": "open",
                    "message": "Goal released for decomposer. Orchestrator should route to decomposer agent.",
                    "hint": "Goal needs decomposition, not more tactic attempts",
                }))?));
            }

            // Direct abandon: just mark this goal as abandoned
            // Siblings continue independently - no cascade
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
                "reason": reason.unwrap_or("exhausted"),
                "previous_state": old_state,
                "new_state": "abandoned",
                "attempt_count": goal.attempt_count,
                "parent": goal.parent,
                "note": "Goal abandoned. Siblings continue independently. Use './bin/lc backtrack <parent>' to abandon entire decomposition.",
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
