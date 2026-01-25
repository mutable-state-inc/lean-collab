//! Warm server that keeps Lean loaded for fast suggestions and verification
//!
//! Runs a Unix socket server that accepts suggestion and verify requests.
//! First request warms up Mathlib (~20s), subsequent requests are fast (~2-5s).

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use crate::config::load_config;

pub const SOCKET_PATH: &str = "/tmp/lean-warm.sock";

/// Request types the warm server can handle
#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum WarmRequestType {
    #[serde(rename = "suggest")]
    Suggest(WarmRequest),
    #[serde(rename = "verify")]
    Verify(VerifyRequest),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WarmRequest {
    pub goal: String,
    pub hypotheses: Vec<String>,
    pub tactic: String,
    #[serde(default)]
    pub imports: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyRequest {
    pub goal: String,
    pub hypotheses: Vec<String>,
    pub tactic: String,
    #[serde(default)]
    pub imports: Vec<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct WarmResponse {
    pub suggestions: Vec<Suggestion>,
    pub time_ms: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VerifyResponse {
    pub success: bool,
    pub time_ms: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stdout: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Suggestion {
    pub tactic: String,
    pub source: String,
}

/// Default imports for warm server
fn default_imports() -> Vec<String> {
    vec![
        "Mathlib.Tactic".to_string(),
        "Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds".to_string(),
        "Mathlib.Analysis.Calculus.Deriv.Basic".to_string(),
        "Mathlib.Analysis.Convex.Function".to_string(),
    ]
}

/// Generate Lean code for suggestion request
fn generate_code(req: &WarmRequest) -> String {
    let imports = if req.imports.is_empty() {
        default_imports()
    } else {
        req.imports.clone()
    };

    let mut code = String::new();
    for imp in imports {
        code.push_str(&format!("import {}\n", imp));
    }
    code.push('\n');

    let valid_hyps: Vec<_> = req.hypotheses.iter().filter(|h| !h.trim().is_empty()).collect();

    // Extract hypothesis names for sanitization
    let hyp_names: Vec<&str> = valid_hyps.iter()
        .filter_map(|h| h.split(':').next().map(|s| s.trim()))
        .collect();

    // Sanitize the goal to fix parsing issues
    let sanitized_goal = sanitize_goal(&req.goal, &hyp_names);

    if valid_hyps.is_empty() {
        code.push_str(&format!("example : {} := by\n  {}\n", sanitized_goal, req.tactic));
    } else {
        let hyp_str = valid_hyps.iter().map(|h| format!("({})", h)).collect::<Vec<_>>().join(" ");
        code.push_str(&format!("example {} : {} := by\n  {}\n", hyp_str, sanitized_goal, req.tactic));
    }

    code
}

/// Run Lean and return output
fn run_lean(code: &str, lean_project: &Path) -> Result<(String, u64)> {
    let suggest_dir = std::env::temp_dir().join("lean-warm");
    std::fs::create_dir_all(&suggest_dir)?;

    let file_path = suggest_dir.join(format!("warm-{}.lean", std::process::id()));
    std::fs::write(&file_path, code)?;

    let start = std::time::Instant::now();
    let output = Command::new("lake")
        .args(["env", "lean", file_path.to_str().unwrap()])
        .current_dir(lean_project)
        .output()
        .context("Failed to run lake env lean")?;

    let elapsed = start.elapsed().as_millis() as u64;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Clean up
    let _ = std::fs::remove_file(&file_path);

    Ok((format!("{}\n{}", stdout, stderr), elapsed))
}

/// Parse suggestions from Lean output
fn parse_suggestions(output: &str) -> Vec<Suggestion> {
    let mut suggestions = Vec::new();
    let lines: Vec<&str> = output.lines().collect();
    let mut i = 0;

    while i < lines.len() {
        if lines[i].contains("Try this:") {
            if i + 1 < lines.len() {
                let tactic_line = lines[i + 1].trim();
                if tactic_line.starts_with('[') {
                    if let Some(bracket_end) = tactic_line.find(']') {
                        let source = &tactic_line[1..bracket_end];
                        let tactic = tactic_line[bracket_end + 1..].trim();
                        suggestions.push(Suggestion {
                            tactic: tactic.to_string(),
                            source: source.to_string(),
                        });
                    }
                }
            }
            i += 2;
            continue;
        }
        i += 1;
    }

    suggestions
}

/// Handle a suggest request
fn handle_suggest(req: WarmRequest, lean_project: &Path) -> WarmResponse {
    let code = generate_code(&req);

    match run_lean(&code, lean_project) {
        Ok((output, time_ms)) => {
            let suggestions = parse_suggestions(&output);
            WarmResponse {
                suggestions,
                time_ms,
                error: None,
            }
        }
        Err(e) => WarmResponse {
            suggestions: vec![],
            time_ms: 0,
            error: Some(e.to_string()),
        },
    }
}

/// Sanitize a goal type to fix common parsing issues:
/// 1. Replace `} \ {` (set difference operator) with explicit Set.diff calls
/// 2. Rename bound variables in set builder notation that conflict with hypothesis names
fn sanitize_goal(goal: &str, hypothesis_names: &[&str]) -> String {
    let mut result = goal.to_string();

    // Fix 1: Convert set difference operator to Set.diff
    // Pattern: `expr1 \ expr2` -> `Set.diff expr1 expr2`
    // Handle the common case: `{...} \ {...}`
    while let Some(backslash_pos) = result.find(" \\ {") {
        // Find the start of the first set (look back for matching `{`)
        let before = &result[..backslash_pos];

        // Use char_indices to handle Unicode correctly
        let char_positions: Vec<(usize, char)> = before.char_indices().collect();
        let mut brace_count = 0;
        let mut start_byte = None;

        // Iterate backwards through characters
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

        // Find the end of the second set (look forward for matching `}`)
        // " \\ {" is 4 bytes
        let after_backslash_start = backslash_pos + 4;
        let after_backslash = &result[after_backslash_start..];
        let mut brace_count = 1; // We already consumed the opening `{`
        let mut end_byte = None;

        for (byte_offset, c) in after_backslash.char_indices() {
            match c {
                '{' => brace_count += 1,
                '}' => {
                    brace_count -= 1;
                    if brace_count == 0 {
                        // End is after this `}`
                        end_byte = Some(after_backslash_start + byte_offset + c.len_utf8());
                        break;
                    }
                }
                _ => {}
            }
        }

        if let (Some(s), Some(e)) = (start_byte, end_byte) {
            let set1 = &result[s..backslash_pos];
            // set2 includes the opening `{` which starts at backslash_pos + 3
            let set2 = &result[backslash_pos + 3..e];
            let replacement = format!("(Set.diff {} {})", set1, set2);
            result = format!("{}{}{}", &result[..s], replacement, &result[e..]);
        } else {
            // Can't parse, give up on this transformation
            break;
        }
    }

    // Fix 2: Rename bound variables in set builder notation if they conflict with hypotheses
    // Pattern: `{x | ...}` where x is in hypothesis_names -> `{x' | ...}` (add prime)
    for &name in hypothesis_names {
        if name.len() == 1 && name.chars().next().is_some_and(|c| c.is_lowercase()) {
            // Single-letter variable name - check if it appears in set builder
            let pattern = format!("{{{}|", name);
            let pattern_space = format!("{{{} |", name);
            if result.contains(&pattern) || result.contains(&pattern_space) {
                // Rename the bound variable by adding a prime
                let new_name = format!("{}'", name);
                result = result.replace(&pattern, &format!("{{{}|", new_name));
                result = result.replace(&pattern_space, &format!("{{{} |", new_name));
                // Also replace uses of the variable in the body (simple heuristic)
                // This is imperfect but catches common cases
                result = result.replace(&format!(" {} ", name), &format!(" {} ", new_name));
                result = result.replace(&format!(" {})", name), &format!(" {})", new_name));
                result = result.replace(&format!("({} ", name), &format!("({} ", new_name));
            }
        }
    }

    result
}

/// Generate Lean code for verify request
fn generate_verify_code(req: &VerifyRequest) -> String {
    let imports = if req.imports.is_empty() {
        vec![
            "Mathlib.Tactic".to_string(),
            "Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic".to_string(),
            "Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds".to_string(),
            "Mathlib.Analysis.Real.Pi.Bounds".to_string(),
            "Mathlib.Analysis.Calculus.Deriv.Basic".to_string(),
            "Mathlib.Analysis.Convex.Function".to_string(),
            "Mathlib.Analysis.Convex.SpecificFunctions.Deriv".to_string(),
            "Mathlib.Topology.Order.Basic".to_string(),
            // Geometry imports for simplex/circumcenter problems
            "Mathlib.Geometry.Euclidean.Circumcenter".to_string(),
            "Mathlib.Analysis.InnerProductSpace.EuclideanDist".to_string(),
        ]
    } else {
        req.imports.clone()
    };

    let mut code = String::new();
    for imp in &imports {
        code.push_str(&format!("import {}\n", imp));
    }
    code.push('\n');

    let valid_hyps: Vec<_> = req.hypotheses.iter().filter(|h| !h.trim().is_empty()).collect();

    // Extract hypothesis names for sanitization
    let hyp_names: Vec<&str> = valid_hyps.iter()
        .filter_map(|h| h.split(':').next().map(|s| s.trim()))
        .collect();

    // Sanitize the goal to fix parsing issues
    let sanitized_goal = sanitize_goal(&req.goal, &hyp_names);

    if valid_hyps.is_empty() {
        code.push_str(&format!("example : {} := by\n  {}\n", sanitized_goal, req.tactic));
    } else {
        let hyp_str = valid_hyps.iter().map(|h| format!("({})", h)).collect::<Vec<_>>().join(" ");
        code.push_str(&format!("example {} : {} := by\n  {}\n", hyp_str, sanitized_goal, req.tactic));
    }

    code
}

/// Handle a verify request
fn handle_verify(req: VerifyRequest, lean_project: &Path) -> VerifyResponse {
    let code = generate_verify_code(&req);

    match run_lean(&code, lean_project) {
        Ok((output, time_ms)) => {
            // Check for errors in output
            // Note: Lean4 errors can be in formats like "error:" or "error(lean.unknownIdentifier):"
            let has_error = output.contains("error:") || output.contains("Error:") || output.contains("error(");
            let has_sorry = output.to_lowercase().contains("sorry");

            let success = !has_error && !has_sorry;

            let error = if has_sorry {
                Some("Proof uses 'sorry' - not a valid proof".to_string())
            } else if has_error {
                // Extract just the error message (handles both "error:" and "error(type):" formats)
                Some(output.lines()
                    .filter(|l| l.contains("error:") || l.contains("Error:") || l.contains("error("))
                    .take(3)
                    .collect::<Vec<_>>()
                    .join("\n"))
            } else {
                None
            };

            VerifyResponse {
                success,
                time_ms,
                error,
                stdout: Some(output),
            }
        }
        Err(e) => VerifyResponse {
            success: false,
            time_ms: 0,
            error: Some(e.to_string()),
            stdout: None,
        },
    }
}

/// Check if warm server is running
pub fn is_server_running() -> bool {
    Path::new(SOCKET_PATH).exists() && UnixStream::connect(SOCKET_PATH).is_ok()
}

/// Send a suggest request to the warm server
pub fn send_request(req: &WarmRequest) -> Result<WarmResponse> {
    let mut stream = UnixStream::connect(SOCKET_PATH)
        .context("Failed to connect to warm server. Start it with: ./bin/lc warm")?;

    let typed_req = WarmRequestType::Suggest(req.clone());
    let request_json = serde_json::to_string(&typed_req)?;
    stream.write_all(request_json.as_bytes())?;
    stream.write_all(b"\n")?;
    stream.flush()?;

    let mut reader = BufReader::new(stream);
    let mut response_line = String::new();
    reader.read_line(&mut response_line)?;

    let response: WarmResponse = serde_json::from_str(&response_line)?;
    Ok(response)
}

/// Send a verify request to the warm server
pub fn send_verify_request(req: &VerifyRequest) -> Result<VerifyResponse> {
    let mut stream = UnixStream::connect(SOCKET_PATH)
        .context("Failed to connect to warm server. Start it with: ./bin/lc warm")?;

    let typed_req = WarmRequestType::Verify(req.clone());
    let request_json = serde_json::to_string(&typed_req)?;
    stream.write_all(request_json.as_bytes())?;
    stream.write_all(b"\n")?;
    stream.flush()?;

    let mut reader = BufReader::new(stream);
    let mut response_line = String::new();
    reader.read_line(&mut response_line)?;

    let response: VerifyResponse = serde_json::from_str(&response_line)?;
    Ok(response)
}

/// Handle a single connection - isolated so errors don't crash the server
fn handle_connection(stream: &mut UnixStream, lean_project: &Path) -> Result<()> {
    let mut reader = BufReader::new(stream.try_clone()?);
    let mut line = String::new();

    if reader.read_line(&mut line).is_ok() && !line.is_empty() {
        // Try to parse as typed request first, fall back to legacy WarmRequest
        if let Ok(typed_req) = serde_json::from_str::<WarmRequestType>(&line) {
            match typed_req {
                WarmRequestType::Suggest(req) => {
                    eprintln!("Suggest: {}...", &req.goal.chars().take(50).collect::<String>());
                    let resp = handle_suggest(req, lean_project);
                    eprintln!("Response: {} suggestions in {}ms", resp.suggestions.len(), resp.time_ms);
                    let resp_json = serde_json::to_string(&resp)?;
                    stream.write_all(resp_json.as_bytes())?;
                    stream.write_all(b"\n")?;
                }
                WarmRequestType::Verify(req) => {
                    eprintln!("Verify: {}...", &req.tactic.chars().take(50).collect::<String>());
                    let resp = handle_verify(req, lean_project);
                    eprintln!("Response: {} in {}ms", if resp.success { "OK" } else { "FAIL" }, resp.time_ms);
                    let resp_json = serde_json::to_string(&resp)?;
                    stream.write_all(resp_json.as_bytes())?;
                    stream.write_all(b"\n")?;
                }
            }
        } else if let Ok(req) = serde_json::from_str::<WarmRequest>(&line) {
            // Legacy format - treat as suggest
            eprintln!("Suggest (legacy): {}...", &req.goal.chars().take(50).collect::<String>());
            let resp = handle_suggest(req, lean_project);
            eprintln!("Response: {} suggestions in {}ms", resp.suggestions.len(), resp.time_ms);
            let resp_json = serde_json::to_string(&resp)?;
            stream.write_all(resp_json.as_bytes())?;
            stream.write_all(b"\n")?;
        } else {
            let err_resp = WarmResponse {
                suggestions: vec![],
                time_ms: 0,
                error: Some("Invalid request format".to_string()),
            };
            let resp_json = serde_json::to_string(&err_resp)?;
            stream.write_all(resp_json.as_bytes())?;
            stream.write_all(b"\n")?;
        }
    }
    Ok(())
}

/// Run the warm server
pub async fn run() -> Result<()> {
    let config = load_config()?;

    let lean_project = config.lean_project_root.as_deref()
        .unwrap_or(&config.workspace);

    // Remove old socket
    if Path::new(SOCKET_PATH).exists() {
        std::fs::remove_file(SOCKET_PATH)?;
    }

    // Warmup
    eprintln!("Warming up Lean (loading Mathlib)...");
    let warmup_req = WarmRequest {
        goal: "True".to_string(),
        hypotheses: vec![],
        tactic: "trivial".to_string(),
        imports: default_imports(),
    };
    let warmup_resp = handle_suggest(warmup_req, lean_project);
    eprintln!("Warmup complete in {}ms", warmup_resp.time_ms);

    // Create server
    let listener = UnixListener::bind(SOCKET_PATH)
        .context("Failed to bind to socket")?;

    // Make socket world-accessible
    std::fs::set_permissions(SOCKET_PATH, std::fs::Permissions::from_mode(0o666))?;

    eprintln!("Lean warm server listening on {}", SOCKET_PATH);
    eprintln!("Press Ctrl+C to stop");

    // Handle shutdown
    let running = Arc::new(AtomicBool::new(true));
    let r = running.clone();
    ctrlc_handler(r);

    // Accept connections
    listener.set_nonblocking(true)?;

    while running.load(Ordering::SeqCst) {
        match listener.accept() {
            Ok((mut stream, _)) => {
                // Handle each connection in a way that won't crash the server
                if let Err(e) = handle_connection(&mut stream, lean_project) {
                    eprintln!("Connection error (non-fatal): {}", e);
                }
            }
            Err(ref e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                std::thread::sleep(std::time::Duration::from_millis(100));
            }
            Err(e) => {
                eprintln!("Accept error: {}", e);
            }
        }
    }

    eprintln!("\nShutting down...");
    let _ = std::fs::remove_file(SOCKET_PATH);

    Ok(())
}

#[cfg(unix)]
fn ctrlc_handler(running: Arc<AtomicBool>) {
    let _ = ctrlc::set_handler(move || {
        running.store(false, Ordering::SeqCst);
    });
}

#[cfg(not(unix))]
fn ctrlc_handler(_running: Arc<AtomicBool>) {}

use std::os::unix::fs::PermissionsExt;
