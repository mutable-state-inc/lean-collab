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

    let proof = match root {
        Some(root_goal) => {
            let proof_body = build_proof(&root_goal, &goals);
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

    // Write to output file
    let output_dir = config.workspace.join("output");
    std::fs::create_dir_all(&output_dir)?;

    let output_path = output
        .map(|p| std::path::PathBuf::from(p))
        .unwrap_or_else(|| output_dir.join("proof.lean"));

    std::fs::write(&output_path, &proof)
        .with_context(|| format!("Failed to write {}", output_path.display()))?;

    let result = serde_json::json!({
        "success": true,
        "output": output_path.display().to_string(),
        "goals_count": goals.len(),
        "proof_length": proof.len(),
        "lean_project": config.lean_project_root.as_ref().map(|p| p.display().to_string()),
    });

    println!("{}", serde_json::to_string_pretty(&result)?);
    Ok(())
}

/// Recursively build proof from goal tree
fn build_proof(goal: &Goal, all_goals: &[Goal]) -> String {
    match &goal.state {
        GoalState::Solved { tactic, .. } => {
            format!("  {}", tactic)
        }
        GoalState::Decomposed { children, strategy, .. } => {
            let mut lines = vec![format!("  {}", strategy)];

            for child_id in children {
                if let Some(child) = all_goals.iter().find(|g| &g.id == child_id) {
                    lines.push(build_proof(child, all_goals));
                }
            }

            lines.join("\n")
        }
        _ => format!("  -- unhandled state: {:?}", goal.state)
    }
}
