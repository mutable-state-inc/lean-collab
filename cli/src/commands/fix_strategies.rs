//! Fix invalid strategies in decomposed goals by extracting valid Lean prefix
//!
//! One-time cleanup for goals that were decomposed before validation was added.

use anyhow::{Context, Result};
use std::process::Command;

use crate::config::{load_config, LoadedConfig};
use crate::ensue::EnsueClient;
use crate::goal::{Goal, GoalState};

/// Try to extract valid Lean tactic from a potentially corrupted strategy
fn extract_valid_lean(strategy: &str) -> String {
    let strategy = strategy.trim();

    // Pattern 1: "tactic args: Natural language description"
    // Find colon followed by space and capital letter
    if let Some(colon_pos) = strategy.find(':') {
        let after_colon = &strategy[colon_pos + 1..];
        if let Some(first_char) = after_colon.trim().chars().next() {
            if first_char.is_uppercase() {
                // This looks like "tactic: Description", extract before colon
                let before = strategy[..colon_pos].trim();
                // But check if this is a valid type annotation like "h : Type"
                // Type annotations have identifiers right before the colon
                let last_word = before.split_whitespace().last().unwrap_or("");
                if !last_word.chars().all(|c| c.is_alphanumeric() || c == '_') {
                    return before.to_string();
                }
            }
        }
    }

    // Pattern 2: "tactic then natural language"
    if let Some(then_pos) = strategy.find(" then ") {
        return strategy[..then_pos].trim().to_string();
    }

    // Pattern 3: "tactic with natural language" (but not "by_cases h : x with ...")
    // Only apply if "with" is followed by natural language, not Lean syntax
    if let Some(with_pos) = strategy.find(" with ") {
        let after_with = &strategy[with_pos + 6..];
        // If after "with" starts with lowercase word (not a variable), likely natural language
        if let Some(first_char) = after_with.trim().chars().next() {
            if first_char.is_lowercase() && !after_with.trim().starts_with("h") {
                return strategy[..with_pos].trim().to_string();
            }
        }
    }

    // Pattern 4: "tactic; natural language" where second part isn't a tactic
    if strategy.contains(';') {
        let parts: Vec<&str> = strategy.split(';').collect();
        if parts.len() >= 2 {
            let second = parts[1].trim();
            // Check if second part starts with a tactic keyword
            let tactic_keywords = ["exact", "apply", "have", "intro", "simp", "rw", "ring",
                                   "linarith", "nlinarith", "constructor", "cases", "by_cases",
                                   "push_neg", "norm_num", "field_simp", "positivity"];
            let second_is_tactic = tactic_keywords.iter().any(|kw| second.starts_with(kw));
            if !second_is_tactic {
                // Second part is natural language, keep only first part
                return parts[0].trim().to_string();
            }
        }
    }

    // Pattern 5: Natural language without any tactic prefix - these should be empty
    let tactic_keywords = ["exact", "apply", "have", "let", "intro", "intros", "simp",
                           "rw", "ring", "linarith", "nlinarith", "constructor", "refine",
                           "cases", "by_cases", "rcases", "obtain", "use", "exists",
                           "push_neg", "by_contra", "norm_num", "field_simp", "positivity",
                           "specialize", "convert", "calc", "show", "suffices"];

    let starts_with_tactic = tactic_keywords.iter().any(|kw| strategy.starts_with(kw));
    if !starts_with_tactic {
        // Doesn't start with a tactic - this is pure natural language
        // Return empty to signal this strategy should be skipped
        return String::new();
    }

    // No pattern matched, return as-is
    strategy.to_string()
}

/// Validate a tactic using Lean compiler
/// Returns true only if Lean accepts the tactic without errors
fn validate_tactic(tactic: &str, config: &LoadedConfig) -> bool {
    if tactic.trim().is_empty() {
        return false;
    }

    let lean_code = format!(
        "import Mathlib.Tactic\nexample : True := by {}",
        tactic
    );

    let lean_project = config.lean_project_root.as_ref()
        .map(|p| p.as_path())
        .unwrap_or(&config.workspace);

    let output = Command::new("lake")
        .args(["env", "lean", "--stdin"])
        .current_dir(lean_project)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            use std::io::Write;
            if let Some(stdin) = child.stdin.as_mut() {
                stdin.write_all(lean_code.as_bytes()).ok();
            }
            child.wait_with_output()
        });

    match output {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            let combined = format!("{}{}", stdout, stderr);

            // Syntax errors indicate invalid Lean code
            let syntax_errors = [
                "unknown tactic",
                "unknown identifier",
                "unexpected",  // catches "unexpected end of input", "unexpected identifier", etc.
                "requires either",
            ];

            // Execution errors are fine - they mean valid syntax but wrong goal
            // e.g., "Tactic 'rewrite' failed" means rw is valid but goal doesn't match

            !syntax_errors.iter().any(|e| combined.to_lowercase().contains(e))
        }
        Err(_) => false,
    }
}

pub async fn run(dry_run: bool) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);

    // List all goals
    let keys = client
        .list_keys(Some(&format!("{}%", config.goals_prefix())), 1000, 0)
        .await?;

    let key_strs: Vec<&str> = keys.iter().map(|k| k.key.as_str()).collect();

    let mut fixes: Vec<(String, String, String)> = Vec::new(); // (goal_id, old, new)
    let mut unfixable: Vec<(String, String)> = Vec::new(); // (goal_id, strategy)

    println!("Scanning {} goals for invalid strategies...", key_strs.len());

    // Fetch and check all goals
    for chunk in key_strs.chunks(100) {
        let memories = client.get_memory(chunk).await?;
        for (key, mem) in memories {
            if let Ok(goal) = serde_json::from_str::<Goal>(&mem.value) {
                if let GoalState::Decomposed { strategy, children, decomposed_at } = &goal.state {
                    // Check if strategy needs fixing
                    let extracted = extract_valid_lean(strategy);

                    if extracted != *strategy {
                        if extracted.is_empty() {
                            // Pure natural language, can't fix
                            unfixable.push((goal.id.clone(), strategy.clone()));
                        } else if validate_tactic(&extracted, &config) {
                            // Valid extraction
                            fixes.push((goal.id.clone(), strategy.clone(), extracted));
                        } else {
                            // Extraction didn't validate
                            unfixable.push((goal.id.clone(), strategy.clone()));
                        }
                    }
                }
            }
        }
    }

    println!("\nFound {} strategies to fix, {} unfixable\n", fixes.len(), unfixable.len());

    // Show what we'll fix
    for (goal_id, old, new) in &fixes {
        println!("Goal: {}", goal_id);
        let old_display: String = old.chars().take(80).collect();
        println!("  Old: {}", old_display);
        println!("  New: {}", new);
        println!();
    }

    if !unfixable.is_empty() {
        println!("\nUnfixable strategies (will be skipped in composition):");
        for (goal_id, strategy) in &unfixable {
            // Safe truncation respecting char boundaries
            let display: String = strategy.chars().take(60).collect();
            println!("  {}: {}", goal_id, display);
        }
    }

    if dry_run {
        println!("\n[DRY RUN] No changes made. Run without --dry-run to apply fixes.");
    } else {
        println!("\nApplying {} fixes...", fixes.len());

        for (goal_id, _old, new) in &fixes {
            let goal_key = format!("{}/{}", config.goals_prefix(), goal_id);

            // Fetch current goal
            if let Some(mem) = client.get(&goal_key).await? {
                let mut goal: Goal = serde_json::from_str(&mem.value)?;

                // Update strategy
                if let GoalState::Decomposed { children, decomposed_at, .. } = &goal.state {
                    goal.state = GoalState::Decomposed {
                        children: children.clone(),
                        strategy: new.clone(),
                        decomposed_at: *decomposed_at,
                    };

                    let goal_json = serde_json::to_string(&goal)?;
                    client.update_memory(&goal_key, &goal_json, false).await?;
                    println!("  Fixed: {}", goal_id);
                }
            }
        }

        println!("\nDone! {} strategies fixed.", fixes.len());
    }

    let result = serde_json::json!({
        "success": true,
        "fixed_count": fixes.len(),
        "unfixable_count": unfixable.len(),
        "dry_run": dry_run,
    });

    println!("\n{}", serde_json::to_string_pretty(&result)?);
    Ok(())
}
