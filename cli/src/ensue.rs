//! Ensue API client for lean-collab
//!
//! All persistent state is stored in Ensue. This client provides
//! async methods for CRUD operations and SSE subscriptions.
//!
//! API endpoints:
//! - HTTP: https://api.ensue-network.ai/ (JSON-RPC)
//! - SSE:  https://events.ensue-network.ai/mcp

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Default API endpoints
pub const DEFAULT_API_URL: &str = "https://api.ensue-network.ai";
pub const DEFAULT_SSE_URL: &str = "https://events.ensue-network.ai/mcp";

/// Ensue API client
#[derive(Debug, Clone)]
pub struct EnsueClient {
    api_url: String,
    sse_url: String,
    api_key: String,
    client: reqwest::Client,
}

/// Memory item for create operations
#[derive(Debug, Clone, Serialize)]
pub struct CreateMemoryItem {
    pub key_name: String,
    pub description: String,
    pub value: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub embed: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub embed_source: Option<EmbedSource>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum EmbedSource {
    Description,
    Value,
}

/// Memory key metadata from list_keys
#[derive(Debug, Clone, Deserialize)]
pub struct KeyMetadata {
    #[serde(alias = "key_name")]
    pub key: String,
    #[serde(default)]
    pub description: Option<String>,
    #[serde(default)]
    pub size: Option<u64>,
    #[serde(default)]
    pub created_at: Option<i64>,
    #[serde(default)]
    pub updated_at: Option<i64>,
}

/// Memory value from get_memory
#[derive(Debug, Clone, Deserialize)]
pub struct Memory {
    #[serde(alias = "key_name")]
    pub key: String,
    pub value: String,
    #[serde(default)]
    pub description: Option<String>,
    #[serde(default)]
    pub size: Option<u64>,
    #[serde(default)]
    pub created_at: Option<i64>,
    #[serde(default)]
    pub updated_at: Option<i64>,
}

/// Search result (includes value)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResult {
    pub key: String,
    pub value: Option<String>,
    pub description: Option<String>,
    #[serde(default)]
    pub score: f64,
}

/// JSON-RPC request
#[derive(Debug, Serialize)]
struct JsonRpcRequest<T: Serialize> {
    jsonrpc: &'static str,
    method: &'static str,
    params: JsonRpcParams<T>,
    id: u32,
}

#[derive(Debug, Serialize)]
struct JsonRpcParams<T: Serialize> {
    name: String,
    arguments: T,
}

/// JSON-RPC response
#[derive(Debug, Deserialize)]
struct JsonRpcResponse {
    result: Option<JsonRpcResult>,
    error: Option<JsonRpcError>,
}

#[derive(Debug, Deserialize)]
struct JsonRpcResult {
    content: Vec<JsonRpcContent>,
}

#[derive(Debug, Deserialize)]
struct JsonRpcContent {
    text: Option<String>,
}

#[derive(Debug, Deserialize)]
struct JsonRpcError {
    message: String,
}

impl EnsueClient {
    /// Create a new client
    pub fn new(api_url: &str, api_key: &str) -> Self {
        Self {
            api_url: api_url.trim_end_matches('/').to_string(),
            sse_url: DEFAULT_SSE_URL.to_string(),
            api_key: api_key.to_string(),
            client: reqwest::Client::new(),
        }
    }

    /// Create client from LoadedConfig
    pub fn from_config(config: &crate::config::LoadedConfig) -> Self {
        Self::new(&config.ensue_api_url, &config.ensue_api_key)
    }

    /// Get SSE URL for streaming events
    pub fn sse_url(&self) -> &str {
        &self.sse_url
    }

    /// Get API key for SSE authentication
    pub fn api_key(&self) -> &str {
        &self.api_key
    }

    /// Make a JSON-RPC call to the Ensue API
    async fn call<T: Serialize>(&self, method: &str, args: T) -> Result<serde_json::Value> {
        let request = JsonRpcRequest {
            jsonrpc: "2.0",
            method: "tools/call",
            params: JsonRpcParams {
                name: method.to_string(),
                arguments: args,
            },
            id: 1,
        };

        let response = self
            .client
            .post(&self.api_url)
            .header("Authorization", format!("Bearer {}", self.api_key))
            .header("Content-Type", "application/json")
            .json(&request)
            .send()
            .await
            .context("Failed to send request to Ensue API")?;

        let status = response.status();
        let text = response.text().await.context("Failed to read response")?;

        // Response comes as "data: {...}" SSE format
        let json_text = text.strip_prefix("data: ").unwrap_or(&text);

        if !status.is_success() {
            anyhow::bail!("Ensue API error ({}): {}", status, json_text);
        }

        let rpc_response: JsonRpcResponse =
            serde_json::from_str(json_text).context("Failed to parse JSON-RPC response")?;

        if let Some(error) = rpc_response.error {
            anyhow::bail!("Ensue API error: {}", error.message);
        }

        let result = rpc_response
            .result
            .and_then(|r| r.content.into_iter().next())
            .and_then(|c| c.text)
            .unwrap_or_else(|| "{}".to_string());

        serde_json::from_str(&result).context("Failed to parse result JSON")
    }

    /// List keys with optional prefix filter
    pub async fn list_keys(
        &self,
        prefix: Option<&str>,
        limit: u32,
        offset: u32,
    ) -> Result<Vec<KeyMetadata>> {
        #[derive(Serialize)]
        struct Args {
            #[serde(skip_serializing_if = "Option::is_none")]
            prefix: Option<String>,
            limit: u32,
            offset: u32,
        }

        let result = self
            .call(
                "list_keys",
                Args {
                    prefix: prefix.map(String::from),
                    limit,
                    offset,
                },
            )
            .await?;

        let keys = result
            .get("keys")
            .and_then(|v| serde_json::from_value::<Vec<KeyMetadata>>(v.clone()).ok())
            .unwrap_or_default();

        Ok(keys)
    }

    /// Get memories by key names (batch, 1-100 keys)
    pub async fn get_memory(&self, key_names: &[&str]) -> Result<HashMap<String, Memory>> {
        #[derive(Serialize)]
        struct Args {
            key_names: Vec<String>,
        }

        let result = self
            .call(
                "get_memory",
                Args {
                    key_names: key_names.iter().map(|s| s.to_string()).collect(),
                },
            )
            .await?;

        // Ensue API returns "results" array with "key_name" field
        let memories = result
            .get("results")
            .and_then(|v| v.as_array())
            .map(|arr| {
                arr.iter()
                    .filter_map(|v| serde_json::from_value::<Memory>(v.clone()).ok())
                    .map(|m| (m.key.clone(), m))
                    .collect()
            })
            .unwrap_or_default();

        Ok(memories)
    }

    /// Get a single memory by key
    pub async fn get(&self, key: &str) -> Result<Option<Memory>> {
        let result = self.get_memory(&[key]).await?;
        Ok(result.get(key).cloned())
    }

    /// Create memories (batch, 1-100 items)
    pub async fn create_memory(&self, items: &[CreateMemoryItem]) -> Result<()> {
        #[derive(Serialize)]
        struct Args {
            items: Vec<CreateMemoryItem>,
        }

        self.call(
            "create_memory",
            Args {
                items: items.to_vec(),
            },
        )
        .await?;

        Ok(())
    }

    /// Update a memory's value
    pub async fn update_memory(&self, key_name: &str, value: &str, embed: bool) -> Result<()> {
        #[derive(Serialize)]
        struct Args {
            key_name: String,
            value: String,
            embed: bool,
        }

        self.call(
            "update_memory",
            Args {
                key_name: key_name.to_string(),
                value: value.to_string(),
                embed,
            },
        )
        .await?;

        Ok(())
    }

    /// Delete memories by key names (batch, 1-100 keys)
    pub async fn delete_memory(&self, key_names: &[&str]) -> Result<()> {
        #[derive(Serialize)]
        struct Args {
            key_names: Vec<String>,
        }

        self.call(
            "delete_memory",
            Args {
                key_names: key_names.iter().map(|s| s.to_string()).collect(),
            },
        )
        .await?;

        Ok(())
    }

    /// Search memories semantically (returns keys and values)
    pub async fn search_memories(
        &self,
        query: &str,
        limit: u32,
        within_days: Option<u32>,
    ) -> Result<Vec<SearchResult>> {
        #[derive(Serialize)]
        struct Args {
            query: String,
            limit: u32,
            #[serde(skip_serializing_if = "Option::is_none")]
            within_days: Option<u32>,
        }

        let result = self
            .call(
                "search_memories",
                Args {
                    query: query.to_string(),
                    limit,
                    within_days,
                },
            )
            .await?;

        let results = result
            .get("results")
            .and_then(|v| serde_json::from_value::<Vec<SearchResult>>(v.clone()).ok())
            .unwrap_or_default();

        Ok(results)
    }

    /// Subscribe to notifications for a memory key
    pub async fn subscribe(&self, key_name: &str) -> Result<()> {
        #[derive(Serialize)]
        struct Args {
            key_name: String,
        }

        self.call(
            "subscribe_to_memory",
            Args {
                key_name: key_name.to_string(),
            },
        )
        .await?;

        Ok(())
    }

    /// Unsubscribe from notifications
    pub async fn unsubscribe(&self, key_name: &str) -> Result<()> {
        #[derive(Serialize)]
        struct Args {
            key_name: String,
        }

        self.call(
            "unsubscribe_from_memory",
            Args {
                key_name: key_name.to_string(),
            },
        )
        .await?;

        Ok(())
    }

    /// List active subscriptions
    pub async fn list_subscriptions(&self) -> Result<Vec<String>> {
        let result = self
            .call("list_subscriptions", serde_json::json!({}))
            .await?;

        let subs = result
            .get("subscriptions")
            .and_then(|v| v.as_array())
            .map(|arr| {
                arr.iter()
                    .filter_map(|v| v.get("key").and_then(|k| k.as_str()).map(String::from))
                    .collect()
            })
            .unwrap_or_default();

        Ok(subs)
    }
}
