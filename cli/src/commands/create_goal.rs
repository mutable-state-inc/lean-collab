//! Create a new goal and auto-subscribe to it
//!
//! Used by decomposer to create child goals. Handles:
//! 1. Goal structure with proper analysis flags
//! 2. Automatic subscription for SSE notifications
//! 3. Validation (depth limits, parent exists)
//! 4. Automatic hypothesis inheritance from parent (with --inherit-hypotheses)

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
    hypotheses: Vec<String>,
    inherit_hypotheses: bool,
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

    // Fetch parent hypotheses if inherit flag is set
    let mut inherited_hypotheses: Vec<String> = Vec::new();

    if let Some(parent_id) = parent {
        let parent_key = format!("{}/{}", config.goals_prefix(), parent_id);
        let parent_mem = client.get(&parent_key).await?;

        match parent_mem {
            None => {
                let result = serde_json::json!({
                    "success": false,
                    "error": "parent_not_found",
                    "message": format!("Parent goal '{}' not found", parent_id),
                });
                println!("{}", serde_json::to_string_pretty(&result)?);
                return Ok(());
            }
            Some(mem) => {
                if inherit_hypotheses {
                    // Parse parent goal and extract hypotheses
                    if let Ok(parent_goal) = serde_json::from_str::<Goal>(&mem.value) {
                        inherited_hypotheses = parent_goal.hypotheses.clone();
                    }
                }
            }
        }
    } else if inherit_hypotheses {
        eprintln!("Warning: --inherit-hypotheses specified but no parent. Ignoring.");
    }

    // Create goal with analysis
    let goal = Goal::analyze(id, goal_type, depth, parent.map(|s| s.to_string()));

    // Build full goal JSON (Goal::analyze creates basic structure, we enhance it)
    // Merge hypotheses: inherited from parent + explicitly provided
    // Filter out empty strings (allows --hypotheses "" for no additional hypotheses)
    let mut all_hypotheses: Vec<String> = inherited_hypotheses;
    let provided: Vec<String> = hypotheses.into_iter().filter(|h| !h.is_empty()).collect();

    // Add provided hypotheses, avoiding duplicates
    for h in provided {
        if !all_hypotheses.contains(&h) {
            all_hypotheses.push(h);
        }
    }

    let filtered_hypotheses = all_hypotheses;

    // VALIDATION: Detect potential free variables in goal_type that lack hypotheses
    // This catches the common decomposer bug of forgetting to pass hypotheses after intro
    // HARD FAIL: Refuse to create goals with missing hypotheses
    let missing_vars = detect_missing_hypotheses(goal_type, &filtered_hypotheses);
    if !missing_vars.is_empty() {
        let suggested_hyps = missing_vars.iter()
            .map(|v| format!("{} : <type>", v))
            .collect::<Vec<_>>()
            .join(";;");

        let result = serde_json::json!({
            "success": false,
            "error": "missing_hypotheses",
            "message": format!(
                "Goal contains variables {} that are not defined in hypotheses. \
                If you used 'intro {}', you MUST add: --hypotheses \"{}\"",
                missing_vars.join(", "),
                missing_vars.join(" "),
                suggested_hyps
            ),
            "missing_variables": missing_vars,
            "suggested_fix": format!("--hypotheses \"{}\"", suggested_hyps),
        });
        println!("{}", serde_json::to_string_pretty(&result)?);
        return Ok(());
    }

    let now = Utc::now().timestamp();
    let goal_json = serde_json::json!({
        "id": id,
        "goal_type": goal_type,
        "state": { "state": "open" },
        "depth": depth,
        "parent": parent,
        "hypotheses": filtered_hypotheses,

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

/// Detect potential free variables in goal_type that aren't covered by hypotheses.
/// Returns a list of variable names that might be missing.
///
/// Heuristics:
/// - Single lowercase letters (a-z) that appear as standalone tokens
/// - Common hypothesis names like hx, ha, hP, etc.
/// - Excludes Lean keywords and common type names
fn detect_missing_hypotheses(goal_type: &str, hypotheses: &[String]) -> Vec<String> {
    use std::collections::HashSet;

    // Build set of variable names defined in hypotheses
    let mut defined_vars: HashSet<String> = HashSet::new();
    for h in hypotheses {
        // Extract variable name from "name : type" pattern
        if let Some(colon_pos) = h.find(':') {
            let var_name = h[..colon_pos].trim();
            defined_vars.insert(var_name.to_string());
        }
    }

    // Lean keywords and common type names to exclude
    let excluded: HashSet<&str> = [
        // Keywords
        "if", "then", "else", "let", "in", "do", "by", "fun", "at", "of", "to",
        // Common types/namespaces
        "Set", "Real", "Nat", "Int", "Bool", "Prop", "Type", "Icc", "Ioo", "Ico", "Ioc",
        // Common functions
        "sin", "cos", "tan", "exp", "log", "pi", "sqrt", "abs",
        // Logical
        "true", "false", "and", "or", "not", "iff",
    ].into_iter().collect();

    let mut potential_vars: Vec<String> = Vec::new();

    // Tokenize goal_type and look for potential free variables
    // A potential free variable is a lowercase identifier that:
    // 1. Is a single letter (a-z) OR starts with 'h' followed by a letter (hypothesis pattern)
    // 2. Is not in the excluded set
    // 3. Is not already defined in hypotheses

    let mut chars = goal_type.chars().peekable();
    while let Some(c) = chars.next() {
        if c.is_alphabetic() || c == '_' {
            // Collect the full identifier
            let mut ident = String::new();
            ident.push(c);
            while let Some(&next) = chars.peek() {
                if next.is_alphanumeric() || next == '_' || next == '\'' {
                    ident.push(chars.next().unwrap());
                } else {
                    break;
                }
            }

            // Check if this looks like a free variable
            let is_single_lowercase = ident.len() == 1 && ident.chars().next().unwrap().is_lowercase();
            let is_hypothesis_name = ident.starts_with('h') && ident.len() >= 2 &&
                ident.chars().nth(1).map_or(false, |c| c.is_uppercase() || c.is_lowercase());

            if (is_single_lowercase || is_hypothesis_name)
                && !excluded.contains(ident.as_str())
                && !defined_vars.contains(&ident)
                && !potential_vars.contains(&ident)
            {
                potential_vars.push(ident);
            }
        }
    }

    potential_vars
}
