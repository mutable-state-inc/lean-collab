//! Create a new goal and auto-subscribe to it
//!
//! Used by decomposer to create child goals. Handles:
//! 1. Goal structure with proper analysis flags
//! 2. Automatic subscription for SSE notifications
//! 3. Validation (depth limits, parent exists)
//! 4. Automatic hypothesis inheritance from parent (with --inherit-hypotheses)
//! 5. Similarity check to detect duplicates/circular decompositions (with --check-similar)

use anyhow::{Context, Result};
use chrono::Utc;

use crate::config::load_config;
use crate::ensue::{CreateMemoryItem, EnsueClient};
use crate::goal::Goal;

/// Similarity thresholds for duplicate/circular detection
const SIMILARITY_BLOCK_THRESHOLD: f64 = 0.92;  // Very likely duplicate - block creation
const SIMILARITY_WARN_THRESHOLD: f64 = 0.85;   // Suspicious - warn but allow

pub async fn run(
    id: &str,
    goal_type: &str,
    parent: Option<&str>,
    depth: u32,
    hypotheses: Vec<String>,
    inherit_hypotheses: bool,
    check_similar: bool,
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

    // VALIDATION: Check for similar/duplicate goals using embeddings
    // This detects circular decompositions and redundant goal creation
    if check_similar {
        let goals_prefix = config.goals_prefix();

        // Search for similar goals using the goal_type as query
        // NOTE: We search 50 results because embeddings are global across all theorems.
        // Old theorem versions (v1, v2, etc.) may have similar goals that could push
        // relevant results from the current theorem out of a small result set.
        let similar = client
            .search_memories(goal_type, 50, None)
            .await
            .unwrap_or_default();

        // Filter to only goals in current theorem and check similarity
        let similar_goals: Vec<_> = similar
            .iter()
            .filter(|r| r.key.starts_with(&goals_prefix) && r.key != format!("{}/{}", goals_prefix, id))
            .collect();

        if let Some(best_match) = similar_goals.first() {
            let score = best_match.score;

            // Extract the goal ID from the key
            let similar_id = best_match.key
                .strip_prefix(&format!("{}/", goals_prefix))
                .unwrap_or(&best_match.key);

            // Check if this is an ancestor (circular decomposition)
            let is_ancestor = is_goal_ancestor(&client, &goals_prefix, parent, similar_id).await;

            if score >= SIMILARITY_BLOCK_THRESHOLD {
                let result = serde_json::json!({
                    "success": false,
                    "error": if is_ancestor { "circular_decomposition" } else { "duplicate_goal" },
                    "message": format!(
                        "Goal is {:.0}% similar to existing goal '{}'. {}",
                        score * 100.0,
                        similar_id,
                        if is_ancestor {
                            "This appears to be a CIRCULAR decomposition - the child goal is equivalent to an ancestor!"
                        } else {
                            "This appears to be a DUPLICATE goal. Consider reusing the existing goal instead."
                        }
                    ),
                    "similar_goal_id": similar_id,
                    "similarity_score": score,
                    "is_ancestor": is_ancestor,
                    "threshold": SIMILARITY_BLOCK_THRESHOLD,
                });
                println!("{}", serde_json::to_string_pretty(&result)?);
                return Ok(());
            } else if score >= SIMILARITY_WARN_THRESHOLD {
                // Warn but allow
                eprintln!(
                    "Warning: Goal is {:.0}% similar to '{}'. {}",
                    score * 100.0,
                    similar_id,
                    if is_ancestor { "Potential circular decomposition!" } else { "Potential duplicate." }
                );
            }
        }
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

/// Check if a goal ID is an ancestor of the current goal being created
/// by walking up the parent chain from the given parent
async fn is_goal_ancestor(
    client: &EnsueClient,
    goals_prefix: &str,
    parent: Option<&str>,
    target_id: &str,
) -> bool {
    let mut current_parent = parent.map(|s| s.to_string());

    while let Some(parent_id) = current_parent {
        if parent_id == target_id {
            return true;
        }

        // Fetch parent goal to get its parent
        let parent_key = format!("{}/{}", goals_prefix, parent_id);
        match client.get(&parent_key).await {
            Ok(Some(mem)) => {
                if let Ok(goal) = serde_json::from_str::<Goal>(&mem.value) {
                    current_parent = goal.parent;
                } else {
                    break;
                }
            }
            _ => break,
        }
    }

    false
}

/// Detect potential free variables in goal_type that aren't covered by hypotheses.
/// Returns a list of variable names that might be missing.
///
/// Heuristics:
/// - Single lowercase letters (a-z) that appear as standalone tokens
/// - Common hypothesis names like hx, ha, hP, etc.
/// - Excludes Lean keywords and common type names
/// - Excludes quantifier-bound variables (∃ x : T, ... or ∀ x : T, ...)
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

    // Extract quantifier-bound variables (∃ x : T, ... or ∀ x : T, ...)
    // These are NOT free variables - they're bound by the quantifier
    let mut bound_vars: HashSet<String> = HashSet::new();

    // Pattern: look for ∃ or ∀ followed by variable name and :
    // Also handle ASCII versions: "exists" and "forall"
    let quantifier_patterns = ["∃", "∀", "exists ", "forall "];
    let mut remaining = goal_type;

    while !remaining.is_empty() {
        let mut found_quantifier = false;
        for pattern in &quantifier_patterns {
            if let Some(pos) = remaining.find(pattern) {
                let after_quantifier = &remaining[pos + pattern.len()..];
                // Skip whitespace and parentheses
                let trimmed = after_quantifier.trim_start_matches(|c: char| c.is_whitespace() || c == '(');
                // Extract the variable name (up to : or whitespace)
                let var_end = trimmed.find(|c: char| c == ':' || c.is_whitespace()).unwrap_or(trimmed.len());
                if var_end > 0 {
                    let var_name = trimmed[..var_end].trim();
                    if !var_name.is_empty() {
                        bound_vars.insert(var_name.to_string());
                    }
                }
                remaining = &remaining[pos + pattern.len()..];
                found_quantifier = true;
                break;
            }
        }
        if !found_quantifier {
            break;
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
    // 4. Is not bound by a quantifier

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
                ident.chars().nth(1).is_some_and(|c| c.is_uppercase() || c.is_lowercase());

            if (is_single_lowercase || is_hypothesis_name)
                && !excluded.contains(ident.as_str())
                && !defined_vars.contains(&ident)
                && !bound_vars.contains(&ident)
                && !potential_vars.contains(&ident)
            {
                potential_vars.push(ident);
            }
        }
    }

    potential_vars
}
