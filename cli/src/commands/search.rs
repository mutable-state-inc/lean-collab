//! Search collective intelligence
//!
//! Allows agents to make pointed queries in specific namespaces:
//! - tactics/solutions/  - successful tactics for similar goals
//! - strategies/         - failed decomposition strategies to avoid

use anyhow::Result;

use crate::config::load_config;
use crate::ensue::EnsueClient;

pub async fn run(query: &str, prefix: Option<&str>, limit: u32) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);

    // Don't modify query - semantic search works better with clean queries
    // Prefix filtering happens post-search
    let search_query = query.to_string();

    let results = client
        .search_memories(&search_query, limit, None)
        .await?;

    // Filter by prefix if specified
    let filtered: Vec<_> = if let Some(p) = prefix {
        results.into_iter().filter(|r| r.key.starts_with(p)).collect()
    } else {
        results
    };

    let result = serde_json::json!({
        "success": true,
        "query": query,
        "prefix": prefix,
        "count": filtered.len(),
        "results": filtered,
    });

    println!("{}", serde_json::to_string_pretty(&result)?);
    Ok(())
}
