//! Subscribe to goal notifications
//!
//! Without subscriptions, `lc listen` won't receive any events.
//! Call this after creating new goals or at session start.

use anyhow::Result;

use crate::config::load_config;
use crate::ensue::EnsueClient;

pub async fn run(goal_id: Option<&str>) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);

    if let Some(gid) = goal_id {
        // Subscribe to specific goal
        let goal_key = format!("{}/{}", config.goals_prefix(), gid);
        client.subscribe(&goal_key).await?;

        let result = serde_json::json!({
            "success": true,
            "subscribed": [goal_key],
        });
        println!("{}", serde_json::to_string_pretty(&result)?);
    } else {
        // Subscribe to all goals for this theorem
        let keys = client
            .list_keys(Some(&format!("{}%", config.goals_prefix())), 1000, 0)
            .await?;

        let mut subscribed = Vec::new();

        for key_meta in &keys {
            // Subscribe to each goal key
            if let Err(e) = client.subscribe(&key_meta.key).await {
                eprintln!("Warning: Failed to subscribe to {}: {}", key_meta.key, e);
            } else {
                subscribed.push(key_meta.key.clone());
            }
        }

        let result = serde_json::json!({
            "success": true,
            "subscribed_count": subscribed.len(),
            "subscribed": subscribed,
        });
        println!("{}", serde_json::to_string_pretty(&result)?);
    }

    Ok(())
}
