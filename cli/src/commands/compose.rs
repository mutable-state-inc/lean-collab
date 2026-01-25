//! Build final composed proof from all solved goals

use anyhow::{Context, Result};

use crate::config::load_config;
use crate::ensue::EnsueClient;
use crate::goal::{Goal, GoalState};

pub async fn run(output: Option<&str>) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);

    // List all goals
    let keys = client
        .list_keys(Some(&format!("{}%", config.goals_prefix())), 1000, 0)
        .await?;

    let key_strs: Vec<&str> = keys.iter().map(|k| k.key.as_str()).collect();

    // Fetch all goals
    let mut goals: Vec<Goal> = Vec::new();
    let mut not_ready = Vec::new();

    if !key_strs.is_empty() {
        for chunk in key_strs.chunks(100) {
            let memories = client.get_memory(chunk).await?;
            for (_key, mem) in memories {
                if let Ok(goal) = serde_json::from_str::<Goal>(&mem.value) {
                    // Check if ready
                    match &goal.state {
                        GoalState::Open | GoalState::Working { .. } | GoalState::Backtracked { .. } => {
                            not_ready.push(goal.id.clone());
                        }
                        _ => {}
                    }
                    goals.push(goal);
                }
            }
        }
    }

    if !not_ready.is_empty() {
        let result = serde_json::json!({
            "success": false,
            "error": "not_ready",
            "message": "Some goals are not yet solved",
            "not_ready_goals": not_ready,
        });
        println!("{}", serde_json::to_string_pretty(&result)?);
        return Ok(());
    }

    if goals.is_empty() {
        let result = serde_json::json!({
            "success": false,
            "error": "no_goals",
            "message": "No goals found for this theorem",
        });
        println!("{}", serde_json::to_string_pretty(&result)?);
        return Ok(());
    }

    // Collect all imports from solved goals
    let mut all_imports: std::collections::HashSet<String> = std::collections::HashSet::new();
    for goal in &goals {
        if let GoalState::Solved { imports, .. } = &goal.state {
            all_imports.extend(imports.iter().cloned());
        }
    }
    // Default to Mathlib.Tactic if no imports specified
    if all_imports.is_empty() {
        all_imports.insert("Mathlib.Tactic".to_string());
    }
    let mut sorted_imports: Vec<_> = all_imports.into_iter().collect();
    sorted_imports.sort();

    // Build proof tree (find root, traverse)
    let root = goals.iter().find(|g| g.parent.is_none());

    let mut proof_errors: Vec<String> = Vec::new();

    let proof = match root {
        Some(root_goal) => {
            let proof_body = build_proof(&root_goal, &goals, &mut proof_errors, 1);
            let imports_str = sorted_imports.iter()
                .map(|i| format!("import {}", i))
                .collect::<Vec<_>>()
                .join("\n");
            format!(
                "{}\n\n-- Theorem: {}\n-- Proved via collaborative decomposition\n\nexample : {} := by\n{}",
                imports_str,
                config.theorem_id,
                root_goal.goal_type,
                proof_body
            )
        }
        None => "-- No root goal found\nsorry".to_string(),
    };

    // Check for errors - if any invalid tactics/axioms/unresolved goals, report them
    let has_errors = !proof_errors.is_empty();

    // Write to output file
    let output_dir = config.workspace.join("output");
    std::fs::create_dir_all(&output_dir)?;

    let output_path = output
        .map(|p| std::path::PathBuf::from(p))
        .unwrap_or_else(|| output_dir.join("proof.lean"));

    std::fs::write(&output_path, &proof)
        .with_context(|| format!("Failed to write {}", output_path.display()))?;

    let result = if has_errors {
        serde_json::json!({
            "success": false,
            "error": "incomplete_proof",
            "message": "Proof has unresolved issues",
            "output": output_path.display().to_string(),
            "goals_count": goals.len(),
            "proof_length": proof.len(),
            "errors": proof_errors,
            "error_count": proof_errors.len(),
            "lean_project": config.lean_project_root.as_ref().map(|p| p.display().to_string()),
        })
    } else {
        serde_json::json!({
            "success": true,
            "output": output_path.display().to_string(),
            "goals_count": goals.len(),
            "proof_length": proof.len(),
            "lean_project": config.lean_project_root.as_ref().map(|p| p.display().to_string()),
        })
    };

    println!("{}", serde_json::to_string_pretty(&result)?);
    Ok(())
}

/// Check if a tactic string looks like valid Lean (not natural language)
/// Real validation happens at decomposition time via Lean compiler check.
/// This is just a simple sanity check for composition.
fn is_valid_tactic(tactic: &str) -> bool {
    let tactic = tactic.trim();

    // Reject empty tactics and sorry
    if tactic.is_empty() || tactic.to_lowercase() == "sorry" {
        return false;
    }

    // Reject tactics with undefined symbols (common in pseudo-code strategies)
    // These indicate the decomposer wrote a proof sketch, not valid Lean
    let invalid_patterns = [
        " g ", " g(", " g)", // undefined function 'g'
        ": g ", // type annotation with undefined 'g'
        "g 0", "g(0", // g applied to 0
        " π", "π/", "π)", // Greek pi (should be Real.pi)
        "(π", // Greek pi in parens
    ];
    for pattern in invalid_patterns {
        if tactic.contains(pattern) {
            return false;
        }
    }

    // Lean tactic keywords - if it starts with one of these, it's valid
    let lean_keywords = [
        "exact", "apply", "have", "let", "show", "suffices",
        "intro", "intros", "rintro", "rcases", "obtain", "cases", "induction",
        "simp", "rw", "rewrite", "ring", "linarith", "nlinarith", "norm_num",
        "field_simp", "positivity", "constructor", "refine", "use", "exists",
        "contradiction", "absurd", "exfalso", "trivial", "decide",
        "calc", "conv", "congr", "ext", "funext", "convert",
        "push_neg", "by_contra", "by_cases",
        "specialize", "generalize", "revert", "clear",
    ];

    for kw in lean_keywords {
        if tactic.starts_with(kw) {
            return true;
        }
    }

    // Structural patterns that indicate valid Lean
    let structural_patterns = ["<;>", "⟨", "⟩", ":=", "·"];
    if structural_patterns.iter().any(|p| tactic.contains(p)) {
        return true;
    }

    false
}

/// Indent all lines of a multi-line string with the given prefix
fn indent_all_lines(text: &str, indent: &str) -> String {
    text.lines()
        .map(|line| {
            if line.trim().is_empty() {
                line.to_string()
            } else {
                format!("{}{}", indent, line)
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Indent continuation lines (all except the first) of a multi-line string
fn indent_continuation_lines(text: &str, indent: &str) -> String {
    let lines: Vec<&str> = text.lines().collect();
    if lines.len() <= 1 {
        return text.to_string();
    }
    let mut result = vec![lines[0].to_string()];
    for line in &lines[1..] {
        if line.trim().is_empty() {
            result.push(line.to_string());
        } else {
            result.push(format!("{}{}", indent, line.trim_start()));
        }
    }
    result.join("\n")
}

/// Check if a strategy contains a `have` or `suffices` that creates 2 subgoals
/// Returns (prefix before have, have declaration without :=) if found
fn parse_have_strategy(strategy: &str) -> Option<(Option<String>, String)> {
    // Look for patterns like "intro x hx; have h : T" or just "have h : T"
    // These create 2 goals: first prove T, then continue with h available

    // Check for `have X : T` without `:=` at the end
    let strategy = strategy.trim();

    // Find the last `have` or `suffices` that doesn't have `:=`
    for keyword in ["have", "suffices"] {
        if let Some(pos) = strategy.rfind(keyword) {
            let after_keyword = &strategy[pos..];
            // Check if this have/suffices has no `:=`
            if !after_keyword.contains(":=") && after_keyword.contains(':') {
                let prefix = if pos > 0 {
                    let before = strategy[..pos].trim().trim_end_matches(';').trim();
                    if before.is_empty() { None } else { Some(before.to_string()) }
                } else {
                    None
                };
                // Extract the have declaration (e.g., "have h : T")
                let have_decl = after_keyword.to_string();
                return Some((prefix, have_decl));
            }
        }
    }
    None
}

/// Extract the tactic from a solved goal, or return sorry if not solved
fn extract_tactic(goal: &Goal) -> String {
    match &goal.state {
        GoalState::Solved { tactic, .. } => tactic.clone(),
        _ => "sorry".to_string(),
    }
}

/// Convert a tactic to term mode if possible
/// "exact term" -> "term"
/// "by exact term" -> "term"
/// Otherwise wrap in "by <tactic>"
fn tactic_to_term(tactic: &str) -> String {
    let tactic = tactic.trim();

    // If it's "exact <term>", extract the term
    if let Some(term) = tactic.strip_prefix("exact ") {
        return term.trim().to_string();
    }

    // If it's "by exact <term>", extract the term
    if let Some(rest) = tactic.strip_prefix("by ") {
        if let Some(term) = rest.trim().strip_prefix("exact ") {
            return term.trim().to_string();
        }
    }

    // Otherwise, wrap in `by` for tactic mode
    format!("by {}", tactic)
}

/// Recursively build proof from goal tree, collecting errors
fn build_proof(goal: &Goal, all_goals: &[Goal], errors: &mut Vec<String>, depth: usize) -> String {
    let indent = "  ".repeat(depth);

    match &goal.state {
        GoalState::Solved { tactic, .. } => {
            if !is_valid_tactic(tactic) {
                errors.push(format!("Goal '{}' has invalid tactic: {}", goal.id, tactic));
                format!("{}sorry -- INVALID: {}", indent, goal.id)
            } else {
                // Handle multi-line tactics: indent all lines properly
                indent_all_lines(tactic, &indent)
            }
        }
        GoalState::Decomposed { children, strategy, .. } => {
            let mut lines = Vec::new();

            // Get all children (including abandoned - they need sorry placeholders)
            let active_children: Vec<_> = children.iter()
                .filter_map(|child_id| all_goals.iter().find(|g| &g.id == child_id))
                .collect();

            // Check if this is a `have`/`suffices` strategy that creates 2 goals
            if let Some((prefix, have_decl)) = parse_have_strategy(strategy) {
                if active_children.len() == 2 {
                    // Emit any prefix (like "intro x hx")
                    if let Some(pre) = prefix {
                        lines.push(format!("{}{}", indent, pre));
                    }

                    // Get the first child's tactic (proves the have)
                    let child0_tactic = extract_tactic(active_children[0]);

                    // Check if child0 tactic is simple (single line, no complex structure)
                    if !child0_tactic.contains('\n') && !child0_tactic.contains("constructor") {
                        // Inline form: have h : T := term_or_by_tactic
                        let term_proof = tactic_to_term(&child0_tactic);
                        lines.push(format!("{}{} := {}", indent, have_decl, term_proof));
                    } else {
                        // Block form for complex multi-line tactics
                        lines.push(format!("{}{} := by", indent, have_decl));
                        let child0_proof = build_proof(active_children[0], all_goals, errors, depth + 1);
                        lines.push(child0_proof);
                    }

                    // Add second child's proof (continues with h available)
                    let child1_proof = build_proof(active_children[1], all_goals, errors, depth);
                    lines.push(child1_proof);

                    return lines.join("\n");
                }
            }

            // Standard handling: emit strategy and children
            if is_valid_tactic(strategy) {
                lines.push(format!("{}{}", indent, strategy));
            }

            let needs_bullets = active_children.len() > 1 && is_valid_tactic(strategy);
            let bullet_continuation_indent = format!("{}  ", indent); // indent for continuation lines after bullet

            for child in active_children {
                // Only increment depth for bulleted children; single child stays at same level
                let child_depth = if needs_bullets { depth + 1 } else { depth };
                let child_proof = build_proof(child, all_goals, errors, child_depth);
                if needs_bullets {
                    // Add bullet point and properly indent multi-line child proofs
                    let trimmed = child_proof.trim_start();
                    let indented = indent_continuation_lines(trimmed, &bullet_continuation_indent);
                    lines.push(format!("{}· {}", indent, indented));
                } else {
                    lines.push(child_proof);
                }
            }

            lines.join("\n")
        }
        GoalState::Axiom { justification, .. } => {
            errors.push(format!("Goal '{}' uses axiom: {}", goal.id, justification));
            format!("{}sorry -- AXIOM: {}", indent, justification)
        }
        GoalState::Abandoned { .. } => {
            // Abandoned goals need sorry placeholder - can't skip because parent tactic
            // (like constructor) may have created this subgoal
            errors.push(format!("Goal '{}' was abandoned (proof incomplete)", goal.id));
            format!("{}sorry -- ABANDONED: {}", indent, goal.id)
        }
        _ => {
            errors.push(format!("Goal '{}' has unresolved state: {:?}", goal.id, goal.state));
            format!("{}sorry -- UNRESOLVED: {:?}", indent, goal.state)
        }
    }
}
