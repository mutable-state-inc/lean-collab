//! Atomically claim a goal for processing (called by hooks on agent spawn)
//!
//! Uses optimistic concurrency: write claim, then re-read to verify we won.
//! This handles race conditions where multiple sessions try to claim simultaneously.
//!
//! Also enforces max_parallel_agents via local slot files with PID tracking.
//! Each slot file contains the PID of the agent holding it. Dead PIDs are reclaimed.

use anyhow::Result;
use chrono::Utc;
use std::time::Duration;
use std::fs;
use std::io::{Read, Write};

use crate::config::load_config;
use crate::ensue::EnsueClient;
use crate::goal::{Goal, GoalState, ClaimRecord, ClaimOutcome};

/// Check if a process with given PID is still alive
fn is_pid_alive(pid: u32) -> bool {
    // On Unix, kill with signal 0 checks if process exists
    #[cfg(unix)]
    {
        let result = unsafe { libc::kill(pid as i32, 0) };
        if result == 0 {
            true // Process exists and we can signal it
        } else {
            // Check errno: EPERM means process exists but we can't signal it
            // ESRCH means no such process
            let errno = std::io::Error::last_os_error().raw_os_error().unwrap_or(0);
            errno == libc::EPERM // EPERM means process exists
        }
    }
    #[cfg(not(unix))]
    {
        // On non-Unix, assume alive (conservative)
        true
    }
}

/// Try to acquire a slot, returns slot number if successful
fn acquire_slot(slots_dir: &std::path::Path, max_slots: u32, our_pid: u32) -> Option<u32> {
    for i in 0..max_slots {
        let slot_file = slots_dir.join(format!("{}.lock", i));

        // Try to read existing PID
        let slot_available = if slot_file.exists() {
            match fs::File::open(&slot_file).and_then(|mut f| {
                let mut contents = String::new();
                f.read_to_string(&mut contents)?;
                Ok(contents)
            }) {
                Ok(contents) => {
                    let contents = contents.trim();
                    if contents.is_empty() {
                        true // Empty file, slot available
                    } else if let Ok(pid) = contents.parse::<u32>() {
                        !is_pid_alive(pid) // Available if PID is dead
                    } else {
                        true // Invalid content, slot available
                    }
                }
                Err(_) => true, // Can't read, assume available
            }
        } else {
            true // File doesn't exist, slot available
        };

        if slot_available {
            // Try to claim this slot by writing our PID
            if let Ok(mut f) = fs::File::create(&slot_file) {
                if f.write_all(our_pid.to_string().as_bytes()).is_ok() {
                    return Some(i);
                }
            }
        }
    }
    None
}

/// Release a slot by clearing the PID file
pub fn release_slot(slots_dir: &std::path::Path, max_slots: u32, our_pid: u32) -> bool {
    for i in 0..max_slots {
        let slot_file = slots_dir.join(format!("{}.lock", i));
        if let Ok(contents) = fs::read_to_string(&slot_file) {
            if contents.trim().parse::<u32>().ok() == Some(our_pid) {
                // This is our slot, clear it
                let _ = fs::write(&slot_file, "");
                return true;
            }
        }
    }
    false
}

/// Generate a unique claim ID for this session
fn generate_claim_id() -> String {
    use std::process;
    let pid = process::id();
    let ts = Utc::now().timestamp_micros();
    format!("claim-{}-{}", pid, ts)
}

pub async fn run(goal_id: &str, agent: Option<&str>, ttl: u64) -> Result<()> {
    let config = load_config()?;
    let client = EnsueClient::from_config(&config);

    // Get parent PID (the agent process that spawned us)
    let parent_pid = std::os::unix::process::parent_id();

    // Try to acquire a local slot (enforces max_parallel_agents)
    let slots_dir = config.slots_dir();
    if slots_dir.exists() {
        if acquire_slot(&slots_dir, config.max_parallel_agents, parent_pid).is_none() {
            // No slots available - at capacity
            let result = serde_json::json!({
                "success": false,
                "error": "capacity_exceeded",
                "goal_id": goal_id,
                "max_parallel_agents": config.max_parallel_agents,
                "message": "All agent slots are in use. Wait for an agent to finish.",
            });
            println!("{}", serde_json::to_string_pretty(&result)?);
            return Ok(());
        }
    }

    // Generate unique claim ID for optimistic concurrency
    let claim_id = generate_claim_id();
    let agent_id = agent.unwrap_or("unknown");
    let full_agent = format!("{}:{}", agent_id, claim_id);
    let goal_key = format!("{}/{}", config.goals_prefix(), goal_id);

    // Fetch current goal
    let memory = client.get(&goal_key).await?;

    let result = match memory {
        Some(mem) => {
            let mut goal: Goal = serde_json::from_str(&mem.value)?;
            let now = Utc::now().timestamp();
            let new_expires_at = now + ttl as i64;

            // Clone state to avoid borrow issues
            let current_state = goal.state.clone();

            match current_state {
                GoalState::Open | GoalState::Backtracked { .. } => {
                    // Attempt to claim - write with our unique claim_id
                    goal.state = GoalState::Working {
                        agent: full_agent.clone(),
                        claimed_at: now,
                        expires_at: new_expires_at,
                    };

                    goal.claim_history.push(ClaimRecord {
                        agent: full_agent.clone(),
                        claimed_at: now,
                        expires_at: new_expires_at,
                        released_at: None,
                        outcome: None,
                    });

                    // Write our claim
                    let goal_json = serde_json::to_string(&goal)?;
                    client.update_memory(&goal_key, &goal_json, false).await?;

                    // Small delay to let concurrent writes settle
                    tokio::time::sleep(Duration::from_millis(50)).await;

                    // Re-read to verify we won the race
                    let verify_memory = client.get(&goal_key).await?;
                    match verify_memory {
                        Some(verify_mem) => {
                            let verify_goal: Goal = serde_json::from_str(&verify_mem.value)?;

                            // Check if OUR claim is the one recorded
                            if let GoalState::Working { agent: recorded_agent, .. } = &verify_goal.state {
                                if recorded_agent == &full_agent {
                                    // We won the race!
                                    serde_json::json!({
                                        "success": true,
                                        "goal_id": goal_id,
                                        "agent": full_agent,
                                        "claimed_at": now,
                                        "expires_at": new_expires_at,
                                        "ttl": ttl,
                                    })
                                } else {
                                    // We lost the race - another session claimed it
                                    serde_json::json!({
                                        "success": false,
                                        "error": "lost_race",
                                        "goal_id": goal_id,
                                        "our_claim": full_agent,
                                        "winner": recorded_agent,
                                        "message": "Another session claimed this goal simultaneously",
                                    })
                                }
                            } else {
                                // Goal state changed (maybe solved already)
                                serde_json::json!({
                                    "success": false,
                                    "error": "state_changed",
                                    "goal_id": goal_id,
                                    "current_state": verify_goal.state,
                                    "message": "Goal state changed during claim attempt",
                                })
                            }
                        }
                        None => {
                            serde_json::json!({
                                "success": false,
                                "error": "verify_failed",
                                "goal_id": goal_id,
                                "message": "Could not verify claim",
                            })
                        }
                    }
                }
                GoalState::Working { agent: current_agent, expires_at: current_expires, .. } => {
                    // Check if expired
                    if current_expires < now {
                        // Expired claim - can take over
                        if let Some(last_claim) = goal.claim_history.last_mut() {
                            last_claim.released_at = Some(now);
                            last_claim.outcome = Some(ClaimOutcome::Expired);
                        }

                        goal.state = GoalState::Working {
                            agent: full_agent.clone(),
                            claimed_at: now,
                            expires_at: new_expires_at,
                        };

                        goal.claim_history.push(ClaimRecord {
                            agent: full_agent.clone(),
                            claimed_at: now,
                            expires_at: new_expires_at,
                            released_at: None,
                            outcome: None,
                        });

                        let goal_json = serde_json::to_string(&goal)?;
                        client.update_memory(&goal_key, &goal_json, false).await?;

                        // Re-verify after taking expired claim
                        tokio::time::sleep(Duration::from_millis(50)).await;
                        let verify_memory = client.get(&goal_key).await?;

                        if let Some(verify_mem) = verify_memory {
                            let verify_goal: Goal = serde_json::from_str(&verify_mem.value)?;
                            if let GoalState::Working { agent: recorded_agent, .. } = &verify_goal.state {
                                if recorded_agent == &full_agent {
                                    serde_json::json!({
                                        "success": true,
                                        "goal_id": goal_id,
                                        "agent": full_agent,
                                        "claimed_at": now,
                                        "expires_at": new_expires_at,
                                        "ttl": ttl,
                                        "previous_claim_expired": true,
                                        "previous_agent": current_agent,
                                    })
                                } else {
                                    serde_json::json!({
                                        "success": false,
                                        "error": "lost_race",
                                        "goal_id": goal_id,
                                        "winner": recorded_agent,
                                    })
                                }
                            } else {
                                serde_json::json!({
                                    "success": false,
                                    "error": "state_changed",
                                    "goal_id": goal_id,
                                })
                            }
                        } else {
                            serde_json::json!({
                                "success": false,
                                "error": "verify_failed",
                                "goal_id": goal_id,
                            })
                        }
                    } else {
                        // Still claimed by someone else
                        serde_json::json!({
                            "success": false,
                            "error": "already_claimed",
                            "goal_id": goal_id,
                            "current_agent": current_agent,
                            "expires_at": current_expires,
                        })
                    }
                }
                other => {
                    serde_json::json!({
                        "success": false,
                        "error": "invalid_state",
                        "goal_id": goal_id,
                        "current_state": other,
                        "message": "Goal is not in a claimable state",
                    })
                }
            }
        }
        None => {
            serde_json::json!({
                "success": false,
                "error": "not_found",
                "goal_id": goal_id,
            })
        }
    };

    println!("{}", serde_json::to_string(&result)?);
    Ok(())
}
