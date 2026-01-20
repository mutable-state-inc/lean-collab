//! lean-collab: Rust CLI for LeanTree collaborative theorem proving
//!
//! This library provides the core functionality for the lean-collab CLI,
//! which orchestrates collaborative theorem proving using Ensue as the
//! single source of truth for all persistent state.

pub mod config;
pub mod ensue;
pub mod error;
pub mod goal;

// Re-export commonly used types
pub use config::Config;
pub use ensue::EnsueClient;
pub use error::{Error, Result};
pub use goal::{Goal, GoalState, Complexity};
