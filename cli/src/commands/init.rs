//! Initialize workspace and validate config

use anyhow::{Context, Result};
use chrono::Utc;

use crate::config::{ensure_workspace, load_config};
use crate::ensue::{CreateMemoryItem, EnsueClient};
use crate::goal::Goal;

pub async fn run(
    _max_agents: u32,
    _max_depth: u32,
    theorem: Option<&str>,
    create_root: bool,
) -> Result<()> {
    // Load and validate config
    let config = load_config()?;

    // Create workspace directories
    ensure_workspace(&config)?;

    // Test Ensue connection
    let client = EnsueClient::from_config(&config);
    let subs = client.list_subscriptions().await?;

    let mut root_created = false;
    let mut root_goal_key = String::new();

    // Create root goal if requested
    if create_root {
        let goal_type = theorem.ok_or_else(|| {
            anyhow::anyhow!("--theorem is required when using --create-root")
        })?;

        // Check if root already exists
        root_goal_key = format!("{}/root", config.goals_prefix());
        let existing = client.get(&root_goal_key).await?;

        if existing.is_some() {
            eprintln!("Root goal already exists, skipping creation");
        } else {
            // Create root goal with analysis
            let goal = Goal::analyze("root", goal_type, 0, None);
            let now = Utc::now().timestamp();

            let goal_json = serde_json::json!({
                "id": "root",
                "goal_type": goal_type,
                "state": { "state": "open" },
                "depth": 0,
                "parent": null,
                "hypotheses": [],

                "has_quantifiers": goal.has_quantifiers,
                "has_transcendentals": goal.has_transcendentals,
                "is_numeric": goal.is_numeric,

                "claim_history": [],
                "strategy_attempts": [],
                "attempt_count": 0,
                "backtrack_count": 0,
                "created_at": now,
            });

            // Create the root goal
            client
                .create_memory(&[CreateMemoryItem {
                    key_name: root_goal_key.clone(),
                    description: format!("Root goal: {}", goal_type),
                    value: serde_json::to_string(&goal_json)?,
                    embed: Some(true),
                    embed_source: None,
                }])
                .await
                .context("Failed to create root goal")?;

            // Auto-subscribe to root
            client
                .subscribe(&root_goal_key)
                .await
                .context("Failed to subscribe to root goal")?;

            root_created = true;
        }
    }

    // Output result
    let mut result = serde_json::json!({
        "success": true,
        "theorem_id": config.theorem_id,
        "workspace": config.workspace.display().to_string(),
        "ensue_url": config.ensue_api_url,
        "config": {
            "max_parallel_agents": config.max_parallel_agents,
            "max_depth": config.max_depth,
            "claim_ttl_seconds": config.claim_ttl_seconds,
        },
        "active_subscriptions": subs.len(),
    });

    if create_root {
        result["root_created"] = serde_json::json!(root_created);
        result["root_goal_key"] = serde_json::json!(root_goal_key);
    }

    println!("{}", serde_json::to_string_pretty(&result)?);
    Ok(())
}
