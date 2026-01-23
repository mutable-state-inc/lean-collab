//! Suggest tactics for a goal using Lean's `apply?` and `exact?`
//!
//! Returns ground-truth suggestions from Lean - no hallucination.
//! This eliminates the "Unknown identifier" errors from guessed lemma names.
//!
//! If a warm server is running (`./bin/lc warm`), uses it for faster responses.

use anyhow::{Context, Result};
use regex::Regex;
use std::process::Command;

use crate::config::load_config;
use crate::ensue::EnsueClient;
use crate::goal::Goal;
use super::warm::{self, WarmRequest};

/// A suggestion from Lean's tactic search
#[derive(Debug, serde::Serialize)]
pub struct Suggestion {
    /// The suggested tactic (e.g., "refine Real.mul_le_sin ?_ ?_")
    pub tactic: String,
    /// Simplified version for direct use (e.g., "Real.mul_le_sin")
    pub lemma: Option<String>,
    /// Remaining subgoals after applying this tactic
    pub subgoals: Vec<String>,
    /// Source tactic that found this (apply?, exact?, etc.)
    pub source: String,
}

/// Parse the output of `apply?` or `exact?`
fn parse_suggestions(output: &str, source: &str) -> Vec<Suggestion> {
    let mut suggestions = Vec::new();

    // Pattern: "Try this:\n  [apply] refine Real.mul_le_sin ?_ ?_"
    // Followed optionally by "-- Remaining subgoals:" and goal lines
    let try_this_re = Regex::new(r"Try this:\s*\n\s*\[(\w+)\]\s*(.+?)(?:\n|$)").unwrap();
    let subgoal_re = Regex::new(r"--\s*⊢\s*(.+)").unwrap();

    let lines: Vec<&str> = output.lines().collect();
    let mut i = 0;

    while i < lines.len() {
        let line = lines[i];

        if line.starts_with("Try this:") {
            // Next line should have the tactic
            if i + 1 < lines.len() {
                let tactic_line = lines[i + 1].trim();

                // Parse [apply] or [exact] prefix
                if let Some(caps) = Regex::new(r"^\[(\w+)\]\s*(.+)$").unwrap().captures(tactic_line) {
                    let tactic_type = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                    let tactic = caps.get(2).map(|m| m.as_str().to_string()).unwrap_or_default();

                    // Extract lemma name from tactic
                    let lemma = extract_lemma_name(&tactic);

                    // Collect subgoals
                    let mut subgoals = Vec::new();
                    let mut j = i + 2;
                    while j < lines.len() {
                        let subgoal_line = lines[j];
                        if subgoal_line.trim().starts_with("-- ⊢") {
                            if let Some(goal) = subgoal_line.trim().strip_prefix("-- ⊢ ") {
                                subgoals.push(goal.to_string());
                            }
                        } else if subgoal_line.starts_with("Try this:") || subgoal_line.trim().is_empty() {
                            break;
                        }
                        j += 1;
                    }

                    suggestions.push(Suggestion {
                        tactic,
                        lemma,
                        subgoals,
                        source: format!("{}:{}", source, tactic_type),
                    });

                    i = j;
                    continue;
                }
            }
        }
        i += 1;
    }

    suggestions
}

/// Extract the main lemma name from a tactic like "refine Real.mul_le_sin ?_ ?_"
fn extract_lemma_name(tactic: &str) -> Option<String> {
    // Common patterns:
    // "refine Real.mul_le_sin ?_ ?_" -> "Real.mul_le_sin"
    // "exact Real.pi_pos" -> "Real.pi_pos"
    // "apply And.intro" -> "And.intro"

    let tactic = tactic.trim();

    // Remove "refine ", "exact ", "apply " prefix
    let without_prefix = tactic
        .strip_prefix("refine ")
        .or_else(|| tactic.strip_prefix("exact "))
        .or_else(|| tactic.strip_prefix("apply "))
        .unwrap_or(tactic);

    // Take everything before the first space or ?
    let lemma = without_prefix
        .split(|c: char| c.is_whitespace() || c == '?')
        .next()
        .map(|s| s.trim_end_matches(|c: char| !c.is_alphanumeric() && c != '.' && c != '_'))
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string());

    lemma
}

/// Generate Lean code for suggestion search
fn generate_suggest_code(goal: &Goal, tactic: &str, imports: &[String]) -> String {
    let mut code = String::new();

    // Imports
    if imports.is_empty() {
        code.push_str("import Mathlib\n\n");
    } else {
        for imp in imports {
            code.push_str(&format!("import {}\n", imp));
        }
        code.push('\n');
    }

    // Build example with hypotheses
    let valid_hypotheses: Vec<_> = goal.hypotheses
        .iter()
        .filter(|h| !h.trim().is_empty())
        .collect();

    if valid_hypotheses.is_empty() {
        code.push_str(&format!(
            "example : {} := by\n  {}\n",
            goal.goal_type, tactic
        ));
    } else {
        let hyp_str = valid_hypotheses
            .iter()
            .map(|h| format!("({})", h))
            .collect::<Vec<_>>()
            .join(" ");

        code.push_str(&format!(
            "example {} : {} := by\n  {}\n",
            hyp_str, goal.goal_type, tactic
        ));
    }

    code
}

pub async fn run(goal_id: &str, tactics: Option<Vec<String>>, imports: Option<Vec<String>>) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);
    let goal_key = format!("{}/{}", config.goals_prefix(), goal_id);

    // Default tactics to try
    let tactics_to_try = tactics.unwrap_or_else(|| {
        vec![
            "apply?".to_string(),
            "exact?".to_string(),
        ]
    });

    let imports = imports.unwrap_or_else(|| {
        vec![
            "Mathlib.Tactic".to_string(),
            "Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds".to_string(),
            "Mathlib.Analysis.Calculus.Deriv.Basic".to_string(),
            "Mathlib.Analysis.Convex.Function".to_string(),
        ]
    });

    // Fetch goal
    let memory = client.get(&goal_key).await?;

    let result = match memory {
        Some(mem) => {
            let goal: Goal = serde_json::from_str(&mem.value)?;

            // Check if warm server is running
            let use_warm = warm::is_server_running();
            if use_warm {
                eprintln!("Using warm server for faster suggestions...");
            }

            let mut all_suggestions = Vec::new();

            for tactic in &tactics_to_try {
                if use_warm {
                    // Use warm server
                    let req = WarmRequest {
                        goal: goal.goal_type.clone(),
                        hypotheses: goal.hypotheses.clone(),
                        tactic: tactic.clone(),
                        imports: imports.clone(),
                    };

                    match warm::send_request(&req) {
                        Ok(resp) => {
                            for s in resp.suggestions {
                                all_suggestions.push(Suggestion {
                                    tactic: s.tactic.clone(),
                                    lemma: extract_lemma_name(&s.tactic),
                                    subgoals: vec![],
                                    source: format!("{}:{}", tactic, s.source),
                                });
                            }
                        }
                        Err(e) => {
                            eprintln!("Warm server error: {}, falling back to cold run", e);
                            // Fall through to cold run below
                            let suggestions = run_cold_suggest(&config, &goal, tactic, &imports, goal_id)?;
                            all_suggestions.extend(suggestions);
                        }
                    }
                } else {
                    // Cold run
                    let suggestions = run_cold_suggest(&config, &goal, tactic, &imports, goal_id)?;
                    all_suggestions.extend(suggestions);
                }
            }

            // Deduplicate by lemma name
            let mut seen_lemmas = std::collections::HashSet::new();
            let unique_suggestions: Vec<_> = all_suggestions
                .into_iter()
                .filter(|s| {
                    if let Some(ref lemma) = s.lemma {
                        seen_lemmas.insert(lemma.clone())
                    } else {
                        true
                    }
                })
                .collect();

            serde_json::json!({
                "success": true,
                "goal_id": goal_id,
                "goal_type": goal.goal_type,
                "suggestions": unique_suggestions,
                "count": unique_suggestions.len(),
                "warm_server": use_warm,
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

/// Run suggestion without warm server (cold run)
fn run_cold_suggest(
    config: &crate::config::LoadedConfig,
    goal: &Goal,
    tactic: &str,
    imports: &[String],
    goal_id: &str,
) -> Result<Vec<Suggestion>> {
    let suggest_dir = config.workspace.join("suggest");
    std::fs::create_dir_all(&suggest_dir)?;

    let lean_project = config.lean_project_root.as_ref()
        .map(|p| p.as_path())
        .unwrap_or(&config.workspace);

    let suggest_file = suggest_dir.join(format!("{}-{}.lean", goal_id, tactic.replace("?", "")));
    let lean_code = generate_suggest_code(goal, tactic, imports);

    std::fs::write(&suggest_file, &lean_code)
        .with_context(|| format!("Failed to write {}", suggest_file.display()))?;

    // Run Lean
    let output = Command::new("lake")
        .args(["env", "lean", suggest_file.to_str().unwrap()])
        .current_dir(lean_project)
        .output()
        .context("Failed to run lake env lean")?;

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Parse suggestions from stdout (Lean outputs "Try this:" there)
    let combined = format!("{}\n{}", stdout, stderr);
    Ok(parse_suggestions(&combined, tactic))
}
