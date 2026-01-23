//! Record a goal as axiomatized with STRICT validation
//!
//! Axioms are last resort. This command REFUSES axiomatization if:
//! - Goal depth < max_depth - 2 (must decompose further)
//! - Reason contains "FALSE", "IMPOSSIBLE", "scaffold", "syntax" (should backtrack)
//! - Goal has quantifiers (should decompose, not axiomatize)
//!
//! Use --force to override (logged as warning).

use anyhow::Result;
use chrono::Utc;

use crate::config::load_config;
use crate::ensue::EnsueClient;
use crate::goal::{ClaimOutcome, Goal, GoalState, StrategyAttempt, StrategyCategory, StrategyStatus};

/// Keywords that indicate the goal should be BACKTRACKED, not axiomatized
const REJECTION_KEYWORDS: &[&str] = &[
    "false", "impossible", "unprovable", "scaffold", "syntax",
    "malformed", "parse error", "bug", "invalid"
];

/// Check if reason contains rejection keywords (case-insensitive)
fn contains_rejection_keyword(reason: &str) -> Option<&'static str> {
    let reason_lower = reason.to_lowercase();
    for &keyword in REJECTION_KEYWORDS {
        if reason_lower.contains(keyword) {
            return Some(keyword);
        }
    }
    None
}

pub async fn run(goal_id: &str, reason: &str, force: bool) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);
    let goal_key = format!("{}/{}", config.goals_prefix(), goal_id);

    // Fetch goal
    let memory = client.get(&goal_key).await?;

    let result = match memory {
        Some(mem) => {
            let mut goal: Goal = serde_json::from_str(&mem.value)?;
            let now = Utc::now().timestamp();

            // === VALIDATION CHECKS ===

            // Check 1: Depth must be >= max_depth - 2
            let depth_threshold = config.max_depth.saturating_sub(2);
            if goal.depth < depth_threshold && !force {
                return Ok(println!("{}", serde_json::to_string_pretty(&serde_json::json!({
                    "success": false,
                    "error": "depth_too_shallow",
                    "goal_id": goal_id,
                    "depth": goal.depth,
                    "threshold": depth_threshold,
                    "max_depth": config.max_depth,
                    "message": format!(
                        "REFUSED: Goal depth {} < threshold {}. Must decompose further or use --force.",
                        goal.depth, depth_threshold
                    ),
                    "suggestion": "Use './bin/lc backtrack' instead to try a different decomposition."
                }))?));
            }

            // Check 2: Reason must not contain rejection keywords
            if let Some(keyword) = contains_rejection_keyword(reason) {
                if !force {
                    return Ok(println!("{}", serde_json::to_string_pretty(&serde_json::json!({
                        "success": false,
                        "error": "invalid_reason",
                        "goal_id": goal_id,
                        "keyword_found": keyword,
                        "message": format!(
                            "REFUSED: Reason contains '{}' which indicates this should be BACKTRACKED, not axiomatized.",
                            keyword
                        ),
                        "suggestion": "Use './bin/lc backtrack' to signal the parent decomposition was wrong."
                    }))?));
                }
            }

            // Check 3: Goals with quantifiers should be decomposed, not axiomatized
            if goal.has_quantifiers && !force {
                return Ok(println!("{}", serde_json::to_string_pretty(&serde_json::json!({
                    "success": false,
                    "error": "has_quantifiers",
                    "goal_id": goal_id,
                    "message": "REFUSED: Goal has quantifiers (∀/∃) and should be decomposed, not axiomatized.",
                    "suggestion": "Use './bin/lc backtrack' to retry with proper decomposition."
                }))?));
            }

            // If force was used, log a warning
            let forced = force && (
                goal.depth < depth_threshold ||
                contains_rejection_keyword(reason).is_some() ||
                goal.has_quantifiers
            );

            // Record strategy attempt (note if forced)
            let strategy_note = if forced {
                format!("axiom (FORCED): {}", reason)
            } else {
                format!("axiom: {}", reason)
            };

            goal.strategy_attempts.push(StrategyAttempt {
                strategy: strategy_note,
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

            let mut result = serde_json::json!({
                "success": true,
                "goal_id": goal_id,
                "reason": reason,
                "axiomatized_at": now,
                "new_state": "axiom",
                "depth": goal.depth,
            });

            if forced {
                result["warning"] = serde_json::json!(
                    "Axiom was FORCED despite validation failures. This may indicate a proof quality issue."
                );
                result["forced"] = serde_json::json!(true);
            }

            result
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
