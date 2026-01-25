//! Error types for lean-collab

#![allow(dead_code)]

use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Configuration error: {0}")]
    Config(String),

    #[error("Ensue API error: {0}")]
    EnsueApi(String),

    #[error("Goal not found: {0}")]
    GoalNotFound(String),

    #[error("Claim failed: {0}")]
    ClaimFailed(String),

    #[error("Verification failed: {0}")]
    VerificationFailed(String),

    #[error("Composition failed: {0}")]
    CompositionFailed(String),

    #[error("Invalid state transition: {0}")]
    InvalidStateTransition(String),

    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),

    #[error("HTTP error: {0}")]
    Http(#[from] reqwest::Error),
}

pub type Result<T> = std::result::Result<T, Error>;
