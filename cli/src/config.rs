//! Configuration management for lean-collab
//!
//! All config is LOCAL to the machine. Ensue only stores the actual work
//! (goals, claims, strategies). This allows multiple machines to work on
//! the same theorem with different local settings.
//!
//! Files:
//! - `.lean-collab.json` - theorem_id, ensue connection
//! - `.ensue-key` - API key
//!
//! Env var overrides for tunable settings:
//! - LEAN_COLLAB_MAX_PARALLEL_AGENTS
//! - LEAN_COLLAB_MAX_DEPTH
//! - LEAN_COLLAB_CLAIM_TTL

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

/// Default Ensue API URL
pub const DEFAULT_ENSUE_URL: &str = "https://api.ensue-network.ai";

/// Default settings
pub const DEFAULT_MAX_PARALLEL_AGENTS: u32 = 12;
pub const DEFAULT_MAX_DEPTH: u32 = 12;
pub const DEFAULT_CLAIM_TTL_SECONDS: u64 = 300; // 5 minutes

/// Environment variable names for tunable settings
pub const ENV_MAX_PARALLEL_AGENTS: &str = "LEAN_COLLAB_MAX_PARALLEL_AGENTS";
pub const ENV_MAX_DEPTH: &str = "LEAN_COLLAB_MAX_DEPTH";
pub const ENV_CLAIM_TTL: &str = "LEAN_COLLAB_CLAIM_TTL";

/// Local configuration (from .lean-collab.json)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Config {
    /// Theorem identifier (namespace prefix in Ensue)
    pub theorem_id: String,

    /// Ensue API URL
    #[serde(default = "default_ensue_url")]
    pub ensue_api_url: String,

    /// Max parallel agents this machine can spawn
    #[serde(default = "default_max_parallel_agents")]
    pub max_parallel_agents: u32,

    /// Max decomposition depth this orchestrator allows
    #[serde(default = "default_max_depth")]
    pub max_depth: u32,

    /// Claim TTL in seconds (how long claims from this machine last)
    #[serde(default = "default_claim_ttl")]
    pub claim_ttl_seconds: u64,

    /// Lean project root (optional, for running lake env lean)
    pub lean_project_root: Option<String>,
}

fn default_ensue_url() -> String {
    DEFAULT_ENSUE_URL.to_string()
}

fn default_max_parallel_agents() -> u32 {
    DEFAULT_MAX_PARALLEL_AGENTS
}

fn default_max_depth() -> u32 {
    DEFAULT_MAX_DEPTH
}

fn default_claim_ttl() -> u64 {
    DEFAULT_CLAIM_TTL_SECONDS
}

/// Resolved configuration with env var overrides applied
#[derive(Debug, Clone)]
pub struct LoadedConfig {
    pub theorem_id: String,
    pub ensue_api_url: String,
    pub ensue_api_key: String,
    pub max_parallel_agents: u32,
    pub max_depth: u32,
    pub claim_ttl_seconds: u64,
    pub workspace: PathBuf,
    pub lean_project_root: Option<PathBuf>,
}

impl LoadedConfig {
    /// Ensue key prefix for this theorem's goals
    pub fn goals_prefix(&self) -> String {
        format!("proofs/{}/goals", self.theorem_id)
    }

    /// Local slots directory for flock semaphore
    pub fn slots_dir(&self) -> PathBuf {
        self.workspace.join(".slots")
    }
}

/// Load config from files with env var overrides for tunable settings
pub fn load_config() -> Result<LoadedConfig> {
    let plugin_root = find_plugin_root()?;
    let config_path = plugin_root.join(".lean-collab.json");
    let key_path = plugin_root.join(".ensue-key");

    // Load config file
    let content = std::fs::read_to_string(&config_path)
        .with_context(|| format!("Failed to read {}", config_path.display()))?;
    let config: Config = serde_json::from_str(&content)
        .with_context(|| "Failed to parse .lean-collab.json")?;

    // Load API key
    let ensue_api_key = std::fs::read_to_string(&key_path)
        .with_context(|| format!("Failed to read {}", key_path.display()))?
        .trim()
        .to_string();

    // Apply env var overrides for tunable settings
    let max_parallel_agents = std::env::var(ENV_MAX_PARALLEL_AGENTS)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(config.max_parallel_agents);

    let max_depth = std::env::var(ENV_MAX_DEPTH)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(config.max_depth);

    let claim_ttl_seconds = std::env::var(ENV_CLAIM_TTL)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(config.claim_ttl_seconds);

    // Resolve workspace
    let workspace = plugin_root.join("workspace").join(&config.theorem_id);

    // Resolve Lean project root
    let lean_project_root = config.lean_project_root.map(|p| {
        let path = PathBuf::from(&p);
        if path.is_absolute() {
            path
        } else {
            plugin_root.join(path)
        }
    });

    Ok(LoadedConfig {
        theorem_id: config.theorem_id,
        ensue_api_url: config.ensue_api_url,
        ensue_api_key,
        max_parallel_agents,
        max_depth,
        claim_ttl_seconds,
        workspace,
        lean_project_root,
    })
}

/// Find plugin root - first from executable location, then from current dir
fn find_plugin_root() -> Result<PathBuf> {
    // Primary: find from executable location (bin/lc -> parent is plugin root)
    if let Ok(exe_path) = std::env::current_exe() {
        // Resolve symlinks to get the real path
        let exe_path = exe_path.canonicalize().unwrap_or(exe_path);
        if let Some(exe_dir) = exe_path.parent() {
            let parent = exe_dir.parent().unwrap_or(exe_dir);
            if parent.join(".lean-collab.json").exists() {
                return Ok(parent.to_path_buf());
            }
        }
    }

    // Fallback: walk up from current dir
    let mut current = std::env::current_dir()?;
    loop {
        if current.join(".lean-collab.json").exists() {
            return Ok(current);
        }

        match current.parent() {
            Some(parent) => current = parent.to_path_buf(),
            None => break,
        }
    }

    anyhow::bail!(
        "Could not find .lean-collab.json. \
        Ensure it exists in the plugin directory."
    )
}

/// Ensure workspace directories exist
pub fn ensure_workspace(config: &LoadedConfig) -> Result<()> {
    let dirs = [
        config.workspace.clone(),
        config.workspace.join("proofs"),
        config.workspace.join("output"),
        config.workspace.join("logs"),
        config.slots_dir(),
    ];

    for dir in &dirs {
        std::fs::create_dir_all(dir)
            .with_context(|| format!("Failed to create {}", dir.display()))?;
    }

    // Create slot files for flock semaphore (one per max_parallel_agents)
    for i in 0..config.max_parallel_agents {
        let slot_file = config.slots_dir().join(format!("{}.lock", i));
        if !slot_file.exists() {
            std::fs::File::create(&slot_file)
                .with_context(|| format!("Failed to create slot file {}", slot_file.display()))?;
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_defaults() {
        assert_eq!(DEFAULT_MAX_PARALLEL_AGENTS, 12);
        assert_eq!(DEFAULT_MAX_DEPTH, 12);
        assert_eq!(DEFAULT_ENSUE_URL, "https://api.ensue-network.ai");
    }
}
