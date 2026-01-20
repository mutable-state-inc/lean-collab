use anyhow::Result;
use clap::{Parser, Subcommand};

mod commands;
mod config;
mod ensue;
mod error;
mod goal;

use commands::*;

#[derive(Parser)]
#[command(name = "lc")]
#[command(about = "LeanTree collaborative theorem proving CLI")]
#[command(version)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Initialize workspace and optionally create root goal
    Init {
        /// Maximum parallel agents
        #[arg(long, default_value = "3")]
        max_agents: u32,

        /// Maximum decomposition depth
        #[arg(long, default_value = "12")]
        max_depth: u32,

        /// Theorem statement (required if --create-root)
        #[arg(long)]
        theorem: Option<String>,

        /// Create root goal and subscribe to it
        #[arg(long)]
        create_root: bool,
    },

    /// Listen to Ensue SSE stream, output events as JSON lines
    Listen {
        /// Filter events by prefix (e.g., "proofs/my-theorem")
        #[arg(long)]
        prefix: Option<String>,
    },

    /// Query comprehensive goal/theorem metadata
    ///
    /// Returns all relevant info in one call: depth, attempts, children,
    /// is_leaf, has_quantifiers, has_transcendentals, strategies_tried, etc.
    Status {
        /// Specific goal ID to query (omit for theorem-level summary)
        goal_id: Option<String>,

        /// Watch mode for continuous updates
        #[arg(long, short)]
        watch: bool,
    },

    /// Atomically claim a goal for processing (called by hooks on agent spawn)
    ///
    /// Claims have a TTL and auto-expire if not released, providing crash safety.
    Claim {
        /// The goal ID to claim
        goal_id: String,

        /// Agent identifier (for tracking who claimed)
        #[arg(long)]
        agent: Option<String>,

        /// Claim TTL in seconds (default: 300 = 5 minutes)
        #[arg(long, default_value = "300")]
        ttl: u64,
    },

    /// Release a claim on a goal (called by hooks on agent exit)
    Unclaim {
        /// The goal ID to unclaim
        goal_id: String,

        /// Agent identifier (must match the claimer)
        #[arg(long)]
        agent: Option<String>,
    },

    /// Verify a tactic for a goal using lake env lean
    Verify {
        /// The goal ID
        #[arg(long)]
        goal: String,

        /// The tactic to verify
        #[arg(long)]
        tactic: String,

        /// Lean imports needed (comma-separated, e.g., "Mathlib.Tactic,Mathlib.Data.Real.Basic")
        #[arg(long, value_delimiter = ',')]
        imports: Option<Vec<String>>,
    },

    /// Build final composed proof from all solved goals
    Compose {
        /// Output file path (default: workspace/output/proof.lean)
        #[arg(long, short)]
        output: Option<String>,
    },

    /// Record a goal as axiomatized (agent decides eligibility)
    Axiomatize {
        /// The goal ID to axiomatize
        goal_id: String,

        /// Justification for axiomatization (required)
        #[arg(long)]
        reason: String,
    },

    /// Undo failed decomposition, mark children abandoned, reopen goal
    Backtrack {
        /// The goal ID to backtrack
        goal_id: String,

        /// Reason for backtracking
        #[arg(long)]
        reason: Option<String>,
    },

    /// Mark a goal as decomposed with its children
    ///
    /// Called by decomposer after creating all child goals.
    Decompose {
        /// The goal ID to mark as decomposed
        goal_id: String,

        /// Child goal IDs (comma-separated)
        #[arg(long, value_delimiter = ',')]
        children: Vec<String>,

        /// Decomposition strategy used (e.g., "intro x hx", "constructor")
        #[arg(long)]
        strategy: String,
    },

    /// Subscribe to goal notifications (required for listen to work)
    ///
    /// Call after creating new goals or at session start.
    /// Without subscriptions, `lc listen` receives nothing.
    Subscribe {
        /// Specific goal ID to subscribe to (omit to subscribe to all)
        goal_id: Option<String>,
    },

    /// Create a new goal (used by decomposer)
    ///
    /// Creates the goal in Ensue with proper structure and auto-subscribes.
    /// Validates depth limits and parent existence.
    CreateGoal {
        /// Goal ID (must be unique)
        #[arg(long)]
        id: String,

        /// Goal type (the proposition to prove)
        #[arg(long, name = "type")]
        goal_type: String,

        /// Parent goal ID
        #[arg(long)]
        parent: Option<String>,

        /// Depth in proof tree
        #[arg(long)]
        depth: u32,

        /// Hypotheses available (comma-separated)
        #[arg(long, value_delimiter = ',')]
        hypotheses: Option<Vec<String>>,
    },

    /// Search collective intelligence for tactics or strategies
    ///
    /// Use to find similar solved goals or failed strategies to avoid.
    Search {
        /// Semantic search query (e.g., "numeric inequality", "IsLeast decomposition")
        query: String,

        /// Namespace prefix to search in
        /// - "tactics/" for successful tactics (default)
        /// - "strategies/" for failed strategies
        #[arg(long)]
        prefix: Option<String>,

        /// Maximum results to return
        #[arg(long, default_value = "10")]
        limit: u32,
    },

}

#[tokio::main]
async fn main() -> Result<()> {
    let cli = Cli::parse();

    let result = match cli.command {
        Commands::Init {
            max_agents,
            max_depth,
            theorem,
            create_root,
        } => init::run(max_agents, max_depth, theorem.as_deref(), create_root).await,

        Commands::Listen { prefix } => listen::run(prefix.as_deref()).await,

        Commands::Status { goal_id, watch } => status::run(goal_id.as_deref(), watch).await,

        Commands::Claim { goal_id, agent, ttl } => claim::run(&goal_id, agent.as_deref(), ttl).await,

        Commands::Unclaim { goal_id, agent } => unclaim::run(&goal_id, agent.as_deref()).await,

        Commands::Verify { goal, tactic, imports } => verify::run(&goal, &tactic, imports).await,

        Commands::Compose { output } => compose::run(output.as_deref()).await,

        Commands::Axiomatize { goal_id, reason } => axiomatize::run(&goal_id, &reason).await,

        Commands::Backtrack { goal_id, reason } => backtrack::run(&goal_id, reason.as_deref()).await,

        Commands::Decompose { goal_id, children, strategy } => {
            decompose::run(&goal_id, children, &strategy).await
        }

        Commands::Subscribe { goal_id } => subscribe::run(goal_id.as_deref()).await,

        Commands::CreateGoal {
            id,
            goal_type,
            parent,
            depth,
            hypotheses,
        } => create_goal::run(&id, &goal_type, parent.as_deref(), depth, hypotheses).await,

        Commands::Search { query, prefix, limit } => search::run(&query, prefix.as_deref(), limit).await,
    };

    // Output errors as JSON for consistent parsing
    if let Err(e) = &result {
        let error_json = serde_json::json!({
            "success": false,
            "error": e.to_string()
        });
        eprintln!("{}", serde_json::to_string(&error_json)?);
    }

    result
}
