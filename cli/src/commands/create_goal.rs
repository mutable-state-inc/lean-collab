//! Create a new goal and auto-subscribe to it
//!
//! Used by decomposer to create child goals. Handles:
//! 1. Goal structure with proper analysis flags
//! 2. Automatic subscription for SSE notifications
//! 3. Validation (depth limits, parent exists)

use anyhow::{Context, Result};
use chrono::Utc;

use crate::config::load_config;
use crate::ensue::{CreateMemoryItem, EnsueClient};
use crate::goal::Goal;

pub async fn run(
    id: &str,
    goal_type: &str,
    parent: Option<&str>,
    depth: u32,
    hypotheses: Option<Vec<String>>,
) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);

    // Check depth limit
    if depth > config.max_depth {
        let result = serde_json::json!({
            "success": false,
            "error": "depth_exceeded",
            "message": format!("Depth {} exceeds max_depth {}", depth, config.max_depth),
        });
        println!("{}", serde_json::to_string_pretty(&result)?);
        return Ok(());
    }

    // If parent specified, verify it exists
    if let Some(parent_id) = parent {
        let parent_key = format!("{}/{}", config.goals_prefix(), parent_id);
        let parent_mem = client.get(&parent_key).await?;
        if parent_mem.is_none() {
            let result = serde_json::json!({
                "success": false,
                "error": "parent_not_found",
                "message": format!("Parent goal '{}' not found", parent_id),
            });
            println!("{}", serde_json::to_string_pretty(&result)?);
            return Ok(());
        }
    }

    // Create goal with analysis
    let goal = Goal::analyze(id, goal_type, depth, parent.map(|s| s.to_string()));

    // Build full goal JSON (Goal::analyze creates basic structure, we enhance it)
    let now = Utc::now().timestamp();
    let goal_json = serde_json::json!({
        "id": id,
        "goal_type": goal_type,
        "state": { "state": "open" },
        "depth": depth,
        "parent": parent,
        "hypotheses": hypotheses.unwrap_or_default(),

        "has_quantifiers": goal.has_quantifiers,
        "has_transcendentals": goal.has_transcendentals,
        "is_numeric": goal.is_numeric,

        "claim_history": [],
        "strategy_attempts": [],
        "attempt_count": 0,
        "backtrack_count": 0,
        "created_at": now,
    });

    let goal_key = format!("{}/{}", config.goals_prefix(), id);

    // Create the goal in Ensue
    client
        .create_memory(&[CreateMemoryItem {
            key_name: goal_key.clone(),
            description: format!("Goal: {}", goal_type),
            value: serde_json::to_string(&goal_json)?,
            embed: Some(true),
            embed_source: None,
        }])
        .await
        .with_context(|| format!("Failed to create goal {}", id))?;

    // Auto-subscribe to the goal
    client
        .subscribe(&goal_key)
        .await
        .with_context(|| format!("Failed to subscribe to goal {}", id))?;

    let result = serde_json::json!({
        "success": true,
        "goal_id": id,
        "goal_key": goal_key,
        "depth": depth,
        "parent": parent,
        "has_quantifiers": goal.has_quantifiers,
        "has_transcendentals": goal.has_transcendentals,
        "is_numeric": goal.is_numeric,
        "subscribed": true,
    });

    println!("{}", serde_json::to_string_pretty(&result)?);
    Ok(())
}
