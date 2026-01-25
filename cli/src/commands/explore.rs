//! Explore: Interactive REPL-like tactic exploration
//!
//! Combines goal state, suggestions, and tactic execution into one command.
//! Allows agents to iteratively explore proofs instead of blind guessing.
//!
//! Usage:
//!   ./bin/lc explore --goal X                    # See state + suggestions
//!   ./bin/lc explore --goal X --tactic "simp"    # Try tactic, see result

use anyhow::{Context, Result};
use std::process::Command;

use crate::config::load_config;
use crate::ensue::EnsueClient;
use crate::goal::{Goal, StrategyCategory, StrategyStatus};
use super::warm::{self, WarmRequest};

/// A previous attempt on this goal (for learning from failures)
#[derive(Debug, serde::Serialize)]
pub struct PreviousAttempt {
    pub strategy: String,
    pub error: Option<String>,
    pub ago: String,  // Human-readable time ago
}

/// Convert timestamp to human-readable "X min ago" format
fn time_ago(timestamp: i64) -> String {
    let now = chrono::Utc::now().timestamp();
    let diff = now - timestamp;

    if diff < 60 {
        format!("{}s ago", diff)
    } else if diff < 3600 {
        format!("{}m ago", diff / 60)
    } else if diff < 86400 {
        format!("{}h ago", diff / 3600)
    } else {
        format!("{}d ago", diff / 86400)
    }
}

/// Extract failed tactic attempts from goal history
fn extract_failed_attempts(goal: &Goal) -> Vec<PreviousAttempt> {
    goal.strategy_attempts
        .iter()
        .filter(|a| {
            // Only show failed tactic attempts (not decompositions or axioms)
            a.category == StrategyCategory::Tactic && a.status == StrategyStatus::Failed
        })
        .map(|a| PreviousAttempt {
            strategy: a.strategy.clone(),
            error: a.error.clone(),
            ago: time_ago(a.attempted_at),
        })
        .collect()
}

/// Result of exploring a goal
#[derive(Debug, serde::Serialize)]
pub struct ExploreResult {
    /// The goal being explored
    pub goal_id: String,
    pub goal_type: String,
    pub hypotheses: Vec<String>,

    /// Previous failed attempts on this goal - DON'T RETRY THESE
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub previous_attempts: Vec<PreviousAttempt>,

    /// If a tactic was provided, what happened
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tactic_result: Option<TacticResult>,

    /// Suggestions from Lean (apply?/exact?)
    pub suggestions: Vec<String>,

    /// Hints for the agent
    pub hints: Vec<String>,
}

#[derive(Debug, serde::Serialize)]
pub struct TacticResult {
    pub tactic: String,
    /// Did the tactic parse and execute?
    pub valid: bool,
    /// Did it complete the proof?
    pub complete: bool,
    /// Remaining goals after this tactic
    pub remaining_goals: Vec<String>,
    /// Error message if invalid
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    /// Time taken
    pub time_ms: u64,
}

/// Default imports for exploration
fn default_imports() -> Vec<String> {
    vec![
        "Mathlib.Tactic".to_string(),
        "Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic".to_string(),
        "Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds".to_string(),
        "Mathlib.Analysis.InnerProductSpace.EuclideanDist".to_string(),
        "Mathlib.Geometry.Euclidean.Circumcenter".to_string(),
        "Mathlib.Analysis.Normed.Group.Basic".to_string(),
    ]
}

/// Sanitize goal for Lean parsing
fn sanitize_goal(goal: &str, hypothesis_names: &[&str]) -> String {
    let mut result = goal.to_string();

    // Fix set difference operator
    while let Some(backslash_pos) = result.find(" \\ {") {
        let before = &result[..backslash_pos];
        let char_positions: Vec<(usize, char)> = before.char_indices().collect();
        let mut brace_count = 0;
        let mut start_byte = None;

        for &(byte_pos, c) in char_positions.iter().rev() {
            match c {
                '}' => brace_count += 1,
                '{' => {
                    brace_count -= 1;
                    if brace_count == 0 {
                        start_byte = Some(byte_pos);
                        break;
                    }
                }
                _ => {}
            }
        }

        let after_backslash_start = backslash_pos + 4;
        let after_backslash = &result[after_backslash_start..];
        let mut brace_count = 1;
        let mut end_byte = None;

        for (byte_offset, c) in after_backslash.char_indices() {
            match c {
                '{' => brace_count += 1,
                '}' => {
                    brace_count -= 1;
                    if brace_count == 0 {
                        end_byte = Some(after_backslash_start + byte_offset + c.len_utf8());
                        break;
                    }
                }
                _ => {}
            }
        }

        if let (Some(s), Some(e)) = (start_byte, end_byte) {
            let set1 = &result[s..backslash_pos];
            let set2 = &result[backslash_pos + 3..e];
            let replacement = format!("(Set.diff {} {})", set1, set2);
            result = format!("{}{}{}", &result[..s], replacement, &result[e..]);
        } else {
            break;
        }
    }

    // Rename conflicting bound variables
    for &name in hypothesis_names {
        if name.len() == 1 && name.chars().next().map_or(false, |c| c.is_lowercase()) {
            let pattern = format!("{{{}|", name);
            let pattern_space = format!("{{{} |", name);
            if result.contains(&pattern) || result.contains(&pattern_space) {
                let new_name = format!("{}'", name);
                result = result.replace(&pattern, &format!("{{{}|", new_name));
                result = result.replace(&pattern_space, &format!("{{{} |", new_name));
                result = result.replace(&format!(" {} ", name), &format!(" {} ", new_name));
                result = result.replace(&format!(" {})", name), &format!(" {})", new_name));
                result = result.replace(&format!("({} ", name), &format!("({} ", new_name));
            }
        }
    }

    result
}

/// Generate Lean code for tactic exploration
fn generate_explore_code(goal: &str, hypotheses: &[String], tactic: &str, imports: &[String]) -> String {
    let imports = if imports.is_empty() { default_imports() } else { imports.to_vec() };

    let mut code = String::new();
    for imp in &imports {
        code.push_str(&format!("import {}\n", imp));
    }
    code.push('\n');

    let valid_hyps: Vec<_> = hypotheses.iter().filter(|h| !h.trim().is_empty()).collect();
    let hyp_names: Vec<&str> = valid_hyps.iter()
        .filter_map(|h| h.split(':').next().map(|s| s.trim()))
        .collect();

    let sanitized_goal = sanitize_goal(goal, &hyp_names);

    if valid_hyps.is_empty() {
        code.push_str(&format!(
            "example : {} := by\n  {}\n",
            sanitized_goal, tactic
        ));
    } else {
        let hyp_str = valid_hyps.iter().map(|h| format!("({})", h)).collect::<Vec<_>>().join(" ");
        code.push_str(&format!(
            "example {} : {} := by\n  {}\n",
            hyp_str, sanitized_goal, tactic
        ));
    }

    code
}

/// Parse remaining goals from Lean output
fn parse_remaining_goals(output: &str) -> Vec<String> {
    let mut goals = Vec::new();
    let lines: Vec<&str> = output.lines().collect();
    let mut in_goals_section = false;

    for line in &lines {
        let trimmed = line.trim();

        if trimmed.contains("unsolved goals") {
            in_goals_section = true;
            continue;
        }

        if in_goals_section {
            // Goal marker: ⊢ goal_type
            if trimmed.starts_with("⊢") {
                let goal = trimmed.strip_prefix("⊢").unwrap_or(trimmed).trim();
                if !goal.is_empty() {
                    goals.push(goal.to_string());
                }
            }
            // Stop at next unrelated error
            else if trimmed.starts_with("error:") && !trimmed.contains("unsolved") {
                break;
            }
        }
    }

    // Also catch standalone goal markers
    if goals.is_empty() {
        for line in &lines {
            let trimmed = line.trim();
            if trimmed.starts_with("⊢ ") && !trimmed.contains("unsolved") {
                let goal = trimmed.strip_prefix("⊢ ").unwrap_or(trimmed).trim();
                if !goal.is_empty() && !goals.contains(&goal.to_string()) {
                    goals.push(goal.to_string());
                }
            }
        }
    }

    goals
}

/// Extract error from Lean output
fn extract_error(output: &str) -> Option<String> {
    let lines: Vec<&str> = output.lines().collect();

    for (i, line) in lines.iter().enumerate() {
        if line.contains("error:") && !line.contains("unsolved goals") {
            let mut error = line.trim().to_string();
            // Add context from next line if helpful
            if i + 1 < lines.len() {
                let next = lines[i + 1].trim();
                if !next.is_empty() && !next.starts_with("error") && next.len() < 200 {
                    error.push_str(" | ");
                    error.push_str(next);
                }
            }
            return Some(error);
        }
    }
    None
}

/// Try a tactic and return the result
fn try_tactic(
    config: &crate::config::LoadedConfig,
    goal: &str,
    hypotheses: &[String],
    tactic: &str,
    imports: &[String],
) -> Result<TacticResult> {
    let explore_dir = std::env::temp_dir().join("lean-explore");
    std::fs::create_dir_all(&explore_dir)?;

    let lean_project = config.lean_project_root.as_ref()
        .map(|p| p.as_path())
        .unwrap_or(&config.workspace);

    let file_path = explore_dir.join(format!("explore-{}.lean", std::process::id()));
    let lean_code = generate_explore_code(goal, hypotheses, tactic, imports);

    std::fs::write(&file_path, &lean_code)?;

    let start = std::time::Instant::now();
    let output = Command::new("lake")
        .args(["env", "lean", file_path.to_str().unwrap()])
        .current_dir(lean_project)
        .output()
        .context("Failed to run lake env lean")?;

    let elapsed = start.elapsed().as_millis() as u64;
    let _ = std::fs::remove_file(&file_path);

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined = format!("{}\n{}", stdout, stderr);

    let has_error = combined.contains("error:");
    let has_unsolved = combined.contains("unsolved goals");
    let complete = !has_error && !has_unsolved;

    // Check for fatal syntax errors that should always be reported
    // These indicate invalid Lean syntax, not just incomplete proofs
    let has_syntax_error = combined.contains("unknown tactic")
        || combined.contains("unknown identifier")
        || combined.contains("expected token");

    let error = if has_syntax_error {
        // Syntax errors are always fatal - extract the error
        extract_error(&combined)
    } else if has_unsolved {
        None // Unsolved goals is expected for partial tactics
    } else {
        extract_error(&combined)
    };

    let remaining_goals = if has_unsolved {
        parse_remaining_goals(&combined)
    } else {
        vec![]
    };

    Ok(TacticResult {
        tactic: tactic.to_string(),
        valid: error.is_none(),
        complete,
        remaining_goals,
        error,
        time_ms: elapsed,
    })
}

/// Get suggestions using warm server or cold run
fn get_suggestions(
    config: &crate::config::LoadedConfig,
    goal: &str,
    hypotheses: &[String],
    imports: &[String],
) -> Vec<String> {
    let mut suggestions = Vec::new();

    // Try warm server first
    if warm::is_server_running() {
        for tactic in &["apply?", "exact?"] {
            let req = WarmRequest {
                goal: goal.to_string(),
                hypotheses: hypotheses.to_vec(),
                tactic: tactic.to_string(),
                imports: if imports.is_empty() { default_imports() } else { imports.to_vec() },
            };

            if let Ok(resp) = warm::send_request(&req) {
                for s in resp.suggestions {
                    if !suggestions.contains(&s.tactic) {
                        suggestions.push(s.tactic);
                    }
                }
            }
        }
    }

    // If warm server not available or no suggestions, try cold
    if suggestions.is_empty() {
        if let Ok(cold_suggestions) = get_cold_suggestions(config, goal, hypotheses, imports) {
            suggestions = cold_suggestions;
        }
    }

    // Limit to top 5 to avoid overwhelming the agent
    suggestions.truncate(5);
    suggestions
}

/// Get suggestions via cold run
fn get_cold_suggestions(
    config: &crate::config::LoadedConfig,
    goal: &str,
    hypotheses: &[String],
    imports: &[String],
) -> Result<Vec<String>> {
    let mut suggestions = Vec::new();

    let explore_dir = std::env::temp_dir().join("lean-explore");
    std::fs::create_dir_all(&explore_dir)?;

    let lean_project = config.lean_project_root.as_ref()
        .map(|p| p.as_path())
        .unwrap_or(&config.workspace);

    for tactic in &["apply?", "exact?"] {
        let file_path = explore_dir.join(format!("suggest-{}-{}.lean", std::process::id(), tactic.replace("?", "")));
        let lean_code = generate_explore_code(goal, hypotheses, tactic, imports);

        std::fs::write(&file_path, &lean_code)?;

        let output = Command::new("lake")
            .args(["env", "lean", file_path.to_str().unwrap()])
            .current_dir(lean_project)
            .output();

        let _ = std::fs::remove_file(&file_path);

        if let Ok(out) = output {
            let combined = format!(
                "{}\n{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );

            // Parse "Try this:" suggestions
            for line in combined.lines() {
                if let Some(idx) = line.find("[") {
                    if let Some(end_idx) = line[idx..].find("]") {
                        let after_bracket = &line[idx + end_idx + 1..].trim();
                        if !after_bracket.is_empty() && !suggestions.contains(&after_bracket.to_string()) {
                            suggestions.push(after_bracket.to_string());
                        }
                    }
                }
            }
        }
    }

    Ok(suggestions)
}

/// Generate hints based on goal structure and results
fn generate_hints(goal: &str, hypotheses: &[String], tactic_result: &Option<TacticResult>, suggestions: &[String], previous_attempts: &[PreviousAttempt]) -> Vec<String> {
    let mut hints = Vec::new();

    // Warn about previous failed attempts
    if !previous_attempts.is_empty() {
        hints.push(format!(
            "⚠ {} previous attempt(s) failed on this goal - see previous_attempts above. DON'T retry these exact tactics!",
            previous_attempts.len()
        ));
    }

    // Hint based on tactic result
    if let Some(ref result) = tactic_result {
        if result.complete {
            hints.push("✓ Proof complete! Run: ./bin/lc verify --goal <id> --tactic \"<your_tactic>\" to record.".to_string());
        } else if !result.valid {
            if let Some(ref err) = result.error {
                if err.contains("unknown identifier") || err.contains("unknown constant") {
                    hints.push("✗ Unknown lemma name. Use one of the suggestions below or check Mathlib docs.".to_string());
                } else if err.contains("type mismatch") {
                    hints.push("✗ Type mismatch. The lemma exists but doesn't apply here. Try a different approach.".to_string());
                } else if err.contains("failed to synthesize") {
                    hints.push("✗ Missing instance. You may need to provide type annotations or use a different lemma.".to_string());
                }
            }
        } else if !result.remaining_goals.is_empty() {
            hints.push(format!("→ {} goal(s) remain. Continue with another tactic.", result.remaining_goals.len()));

            // Analyze remaining goals for hints
            for remaining in &result.remaining_goals {
                if remaining.contains("‖") && remaining.contains("=") {
                    hints.push("  Tip: For norm equalities, try `norm_num`, `simp [norm_eq_abs]`, or `congrArg`".to_string());
                }
                if remaining.contains("dist") {
                    hints.push("  Tip: For distance goals, try `simp only [dist_eq_norm]` or `EuclideanSpace.dist_eq`".to_string());
                }
            }
        }
    }

    // Hints based on goal structure (when no tactic yet)
    if tactic_result.is_none() {
        if goal.contains("dist") {
            hints.push("Goal involves distance. Common tactics: simp [dist_eq_norm], EuclideanSpace.dist_eq".to_string());
        }
        if goal.contains("∈") && goal.contains("Set") {
            hints.push("Goal involves set membership. Try: exact ⟨_, _⟩, constructor, or simp".to_string());
        }
        if goal.contains("∀") {
            hints.push("Goal has universal quantifier. Try: intro, or apply a lemma that matches.".to_string());
        }
        if goal.contains("∃") {
            hints.push("Goal has existential. Try: use <witness>, refine ⟨_, ?_⟩, or exact ⟨_, _⟩".to_string());
        }

        // Check if hypotheses might help
        for hyp in hypotheses {
            if hyp.contains(":") {
                let parts: Vec<&str> = hyp.splitn(2, ':').collect();
                if parts.len() == 2 {
                    let hyp_name = parts[0].trim();
                    let hyp_type = parts[1].trim();

                    // Check if hypothesis type relates to goal
                    if goal.contains("color") && hyp_type.contains("color") {
                        hints.push(format!("Hypothesis `{}` involves color - likely relevant.", hyp_name));
                    }
                    if goal.contains("dist") && hyp_type.contains("dist") {
                        hints.push(format!("Hypothesis `{}` involves distance - try `exact {}` or `apply {}`.", hyp_name, hyp_name, hyp_name));
                    }
                }
            }
        }
    }

    // Always show suggestion hint if we have some
    if !suggestions.is_empty() {
        hints.push(format!("{} suggestion(s) from Lean's apply?/exact? - these are guaranteed to type-check.", suggestions.len()));
    }

    hints
}

pub async fn run(goal_id: &str, tactic: Option<&str>, imports: Option<Vec<String>>) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);
    let goal_key = format!("{}/{}", config.goals_prefix(), goal_id);
    let imports = imports.unwrap_or_default();

    // Fetch goal
    let memory = client.get(&goal_key).await?;

    let result = match memory {
        Some(mem) => {
            let goal: Goal = serde_json::from_str(&mem.value)?;

            // Extract previous failed attempts - provers should NOT retry these
            let previous_attempts = extract_failed_attempts(&goal);

            // Try tactic if provided
            let tactic_result = if let Some(t) = tactic {
                Some(try_tactic(&config, &goal.goal_type, &goal.hypotheses, t, &imports)?)
            } else {
                None
            };

            // Get suggestions (skip if proof already complete)
            let suggestions = if tactic_result.as_ref().map(|r| r.complete).unwrap_or(false) {
                vec![]
            } else {
                // For remaining goals, get suggestions for the first one
                let search_goal = tactic_result.as_ref()
                    .and_then(|r| r.remaining_goals.first())
                    .map(|s| s.as_str())
                    .unwrap_or(&goal.goal_type);

                get_suggestions(&config, search_goal, &goal.hypotheses, &imports)
            };

            // Generate hints
            let hints = generate_hints(&goal.goal_type, &goal.hypotheses, &tactic_result, &suggestions, &previous_attempts);

            let explore_result = ExploreResult {
                goal_id: goal_id.to_string(),
                goal_type: goal.goal_type.clone(),
                hypotheses: goal.hypotheses.clone(),
                previous_attempts,
                tactic_result,
                suggestions,
                hints,
            };

            serde_json::json!({
                "success": true,
                "explore": explore_result,
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
