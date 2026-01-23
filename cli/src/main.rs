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

        /// Output file path (defaults to stdout)
        #[arg(long, short)]
        output: Option<String>,
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

    /// Record a goal as axiomatized (with strict validation)
    ///
    /// REFUSES axiomatization if:
    /// - depth < max_depth - 2 (must decompose further)
    /// - reason contains FALSE/scaffold/syntax (should backtrack)
    /// - goal has quantifiers (should decompose)
    Axiomatize {
        /// The goal ID to axiomatize
        goal_id: String,

        /// Justification for axiomatization (required)
        #[arg(long)]
        reason: String,

        /// Force axiomatization despite validation failures (use sparingly)
        #[arg(long, default_value = "false")]
        force: bool,
    },

    /// Undo failed decomposition, mark children abandoned, reopen goal
    Backtrack {
        /// The goal ID to backtrack
        goal_id: String,

        /// Reason for backtracking
        #[arg(long)]
        reason: Option<String>,
    },

    /// Manually abandon a goal (for cleanup or error recovery)
    ///
    /// Requires at least 10 tactic attempts for leaf goals before abandoning.
    /// Use --force to override (for cleanup/error recovery only).
    Abandon {
        /// The goal ID to abandon
        goal_id: String,

        /// Reason for abandonment
        #[arg(long)]
        reason: Option<String>,

        /// Force abandonment even if minimum attempts not reached
        #[arg(long, default_value = "false")]
        force: bool,
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

        /// Hypotheses available (semicolon-semicolon separated: ;;).
        /// Example: "x : ℝ;;hx : x ∈ Set.Icc 0 Real.pi;;hc : ∀ y ∈ S, P y"
        /// Use empty string "" for goals with no hypotheses.
        #[arg(long)]
        hypotheses: Option<String>,

        /// Automatically inherit hypotheses from parent goal (DEFAULT: true).
        /// Merges parent's hypotheses with any explicitly provided ones.
        /// Use --no-inherit-hypotheses to disable (rarely needed).
        #[arg(long, default_value = "true", action = clap::ArgAction::Set)]
        inherit_hypotheses: bool,
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

    /// Fix invalid strategies in decomposed goals
    ///
    /// One-time cleanup for goals decomposed before validation was added.
    /// Extracts valid Lean prefix from corrupted strategies and updates them.
    FixStrategies {
        /// Dry run - show what would be fixed without making changes
        #[arg(long)]
        dry_run: bool,
    },

    /// Get tactic suggestions from Lean's apply?/exact?
    ///
    /// Returns ground-truth lemmas that Lean knows can apply to this goal.
    /// Use this instead of guessing lemma names to avoid "Unknown identifier" errors.
    Suggest {
        /// The goal ID to get suggestions for
        #[arg(long)]
        goal: String,

        /// Tactics to try (default: apply?, exact?)
        #[arg(long, value_delimiter = ',')]
        tactics: Option<Vec<String>>,

        /// Lean imports needed (default: Mathlib)
        #[arg(long, value_delimiter = ',')]
        imports: Option<Vec<String>>,
    },

    /// Start warm server to keep Lean/Mathlib loaded
    ///
    /// Runs a background server that accepts suggestion requests.
    /// First request warms up Mathlib (~20s), subsequent requests are fast (~2-5s).
    /// The suggest command will automatically use this server when running.
    Warm,
}

/// Parse hypotheses string by splitting on ";;" delimiter.
/// Using ";;" because it never appears in valid Lean syntax, unlike commas.
/// Example: "x : ℝ;;hc : ∀ y ∈ Set.Icc 0 1, P y" -> ["x : ℝ", "hc : ∀ y ∈ Set.Icc 0 1, P y"]
fn parse_hypotheses(input: Option<&str>) -> Vec<String> {
    let Some(s) = input else {
        return Vec::new();
    };

    let s = s.trim();
    if s.is_empty() {
        return Vec::new();
    }

    // Split on ";;" delimiter - never appears in valid Lean
    s.split(";;")
        .map(|h| h.trim().to_string())
        .filter(|h| !h.is_empty())
        .collect()
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

        Commands::Listen { prefix, output } => listen::run(prefix.as_deref(), output.as_deref()).await,

        Commands::Status { goal_id, watch } => status::run(goal_id.as_deref(), watch).await,

        Commands::Claim { goal_id, agent, ttl } => claim::run(&goal_id, agent.as_deref(), ttl).await,

        Commands::Unclaim { goal_id, agent } => unclaim::run(&goal_id, agent.as_deref()).await,

        Commands::Verify { goal, tactic, imports } => verify::run(&goal, &tactic, imports).await,

        Commands::Compose { output } => compose::run(output.as_deref()).await,

        Commands::Axiomatize { goal_id, reason, force } => axiomatize::run(&goal_id, &reason, force).await,

        Commands::Backtrack { goal_id, reason } => backtrack::run(&goal_id, reason.as_deref()).await,

        Commands::Abandon { goal_id, reason, force } => abandon::run(&goal_id, reason.as_deref(), force).await,

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
            inherit_hypotheses,
        } => {
            let parsed_hypotheses = parse_hypotheses(hypotheses.as_deref());
            create_goal::run(&id, &goal_type, parent.as_deref(), depth, parsed_hypotheses, inherit_hypotheses).await
        }

        Commands::Search { query, prefix, limit } => search::run(&query, prefix.as_deref(), limit).await,

        Commands::FixStrategies { dry_run } => fix_strategies::run(dry_run).await,

        Commands::Suggest { goal, tactics, imports } => suggest::run(&goal, tactics, imports).await,

        Commands::Warm => warm::run().await,
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
