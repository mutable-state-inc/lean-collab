//! Goal data structures and state machine
//!
//! The goal tree is append-only. All state transitions, claims, and attempts
//! are preserved for shared memory, thought logging, and later analysis.

use serde::{Deserialize, Serialize};

/// Complexity classification for routing decisions
/// Note: The SKILL.md contains the actual routing logic.
/// This enum provides structural analysis the CLI can detect syntactically.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Complexity {
    /// Pure numeric (norm_num, decide, ring)
    Trivial,
    /// Decidable procedures (native_decide, simp)
    Decidable,
    /// Needs Mathlib lemma lookup
    Discoverable,
    /// Transcendental functions, likely needs decomposition
    Analytical,
    /// Has quantifiers, must decompose
    Structural,
    /// Cannot determine syntactically - Claude must use judgment to classify
    /// At shallow depth: likely needs decomposition
    /// At deep depth: likely provable, try tactics first
    NeedsJudgment,
}

/// Outcome of a claim (what happened while agent held the goal)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ClaimOutcome {
    /// Agent released without solving (will retry or hand off)
    Released,
    /// Claim expired (agent crashed or timed out)
    Expired,
    /// Goal was solved
    Solved,
    /// Goal was decomposed into children
    Decomposed,
    /// Goal was axiomatized
    Axiomatized,
}

/// Record of a claim (preserved in history)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClaimRecord {
    pub agent: String,
    pub claimed_at: i64,
    pub expires_at: i64,
    pub released_at: Option<i64>,
    pub outcome: Option<ClaimOutcome>,
}

/// Goal state machine
/// Clear states with defined transitions
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "state", rename_all = "snake_case")]
pub enum GoalState {
    /// Available for work
    Open,

    /// Claimed by an agent (with TTL)
    Working {
        agent: String,
        claimed_at: i64,
        expires_at: i64,
    },

    /// Successfully proved
    Solved {
        tactic: String,
        #[serde(default)]
        imports: Vec<String>,
        solved_at: i64,
    },

    /// Decomposed into children
    Decomposed {
        children: Vec<String>,
        strategy: String,
        decomposed_at: i64,
    },

    /// Marked as axiom
    Axiom {
        justification: String,
        axiomatized_at: i64,
    },

    /// Backtracked decomposition (re-opened for different strategy)
    Backtracked {
        attempt: u32,
        backtracked_at: i64,
    },

    /// All strategies exhausted
    Exhausted {
        attempts: u32,
        exhausted_at: i64,
    },

    /// Children of backtracked decomposition (preserved but inactive)
    Abandoned {
        parent_backtrack_attempt: u32,
        abandoned_at: i64,
    },
}

/// Strategy attempt record (preserved for learning)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StrategyAttempt {
    pub strategy: String,
    pub category: StrategyCategory,
    pub attempted_at: i64,
    pub duration_ms: Option<u64>,
    pub status: StrategyStatus,
    pub error: Option<String>,
    pub agent: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StrategyCategory {
    Tactic,
    Decomposition,
    Axiom,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StrategyStatus {
    Attempted,
    Succeeded,
    Failed,
}

/// Full goal record
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Goal {
    pub id: String,
    pub goal_type: String,
    pub state: GoalState,
    pub depth: u32,
    pub parent: Option<String>,

    /// Hypotheses in scope (e.g., ["x : ℝ", "hx : x ∈ Set.Icc 0 1"])
    /// Stored when decomposing so verification can reconstruct context
    #[serde(default)]
    pub hypotheses: Vec<String>,

    // Structural analysis (syntactic, CLI can detect)
    pub has_quantifiers: bool,
    pub has_transcendentals: bool,
    pub is_numeric: bool,

    // History (append-only, never deleted)
    pub claim_history: Vec<ClaimRecord>,
    pub strategy_attempts: Vec<StrategyAttempt>,

    // Counters (derived from history, cached for convenience)
    pub attempt_count: u32,
    pub backtrack_count: u32,

    // Metadata
    pub created_at: i64,
}

impl Goal {
    /// Analyze goal type string for structural properties
    pub fn analyze(id: &str, goal_type: &str, depth: u32, parent: Option<String>) -> Self {
        Self {
            id: id.to_string(),
            goal_type: goal_type.to_string(),
            state: GoalState::Open,
            depth,
            parent,
            hypotheses: vec![],
            has_quantifiers: Self::detect_quantifiers(goal_type),
            has_transcendentals: Self::detect_transcendentals(goal_type),
            is_numeric: Self::detect_numeric(goal_type),
            claim_history: vec![],
            strategy_attempts: vec![],
            attempt_count: 0,
            backtrack_count: 0,
            created_at: chrono::Utc::now().timestamp(),
        }
    }

    /// Check for quantifiers (∀, ∃, forall, exists)
    fn detect_quantifiers(goal_type: &str) -> bool {
        goal_type.contains('∀')
            || goal_type.contains('∃')
            || goal_type.contains("forall")
            || goal_type.contains("exists")
            || goal_type.contains("\\forall")
            || goal_type.contains("\\exists")
    }

    /// Check for transcendental functions
    fn detect_transcendentals(goal_type: &str) -> bool {
        let transcendentals = [
            "Real.exp", "Real.log", "Real.sin", "Real.cos", "Real.tan",
            "Real.arcsin", "Real.arccos", "Real.arctan", "Real.sqrt",
            "Real.pi", "rexp", "log", "sin", "cos", "tan",
        ];
        transcendentals.iter().any(|t| goal_type.contains(t))
    }

    /// Check if goal is purely numeric
    fn detect_numeric(goal_type: &str) -> bool {
        // Simple heuristic: only numbers, arithmetic ops, comparisons
        let non_numeric_indicators = [
            "∀", "∃", "forall", "exists", "fun", "λ", "→", "->",
            "Real.", "Nat.", "Int.", "List.", "Set.", "Finset.",
        ];
        !non_numeric_indicators.iter().any(|ind| goal_type.contains(ind))
            && goal_type.chars().all(|c| {
                c.is_numeric()
                    || c.is_whitespace()
                    || "+-*/^=<>≤≥()[]{}.,".contains(c)
            })
    }

    /// Compute complexity based on structural analysis
    /// Returns Unknown for cases that need Claude's judgment
    pub fn complexity(&self) -> Complexity {
        if self.is_numeric {
            Complexity::Trivial
        } else if self.has_quantifiers {
            Complexity::Structural
        } else if self.has_transcendentals {
            Complexity::Analytical
        } else {
            // Cannot determine syntactically - Claude must use judgment
            // At shallow depth: likely needs decomposition (e.g., "color P = color 0")
            // At deep depth: likely a leaf, try tactics first
            Complexity::NeedsJudgment
        }
    }

    /// Check if this is a leaf (no children, not decomposed)
    pub fn is_leaf(&self) -> bool {
        !matches!(self.state, GoalState::Decomposed { .. })
    }

    /// Check if goal can potentially be decomposed further
    ///
    /// Returns true if decomposition is possible (not at max depth).
    /// For Unknown complexity, returns true to let Claude decide.
    pub fn can_decompose(&self, max_depth: u32) -> bool {
        if self.depth >= max_depth {
            return false;
        }

        // For known complex types, definitely can decompose
        // For NeedsJudgment, also return true - Claude will decide if needed
        matches!(
            self.complexity(),
            Complexity::Analytical | Complexity::Structural | Complexity::NeedsJudgment
        )
    }

    /// Get current claim if working and not expired
    pub fn current_claim(&self) -> Option<&ClaimRecord> {
        if let GoalState::Working { .. } = &self.state {
            self.claim_history.last()
        } else {
            None
        }
    }

    /// Get strategies that succeeded on this goal
    pub fn successful_strategies(&self) -> Vec<&StrategyAttempt> {
        self.strategy_attempts
            .iter()
            .filter(|s| s.status == StrategyStatus::Succeeded)
            .collect()
    }

    /// Get strategies that failed on this goal
    pub fn failed_strategies(&self) -> Vec<&StrategyAttempt> {
        self.strategy_attempts
            .iter()
            .filter(|s| s.status == StrategyStatus::Failed)
            .collect()
    }
}

/// Summary of theorem status
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TheoremStatus {
    pub theorem_id: String,
    pub open: u32,
    pub working: u32,
    pub solved: u32,
    pub decomposed: u32,
    pub axiomatized: u32,
    pub exhausted: u32,
    pub abandoned: u32,
    pub backtracked: u32,
    pub total: u32,
    pub ready_to_compose: bool,
    pub open_goals: Vec<String>,
    pub working_goals: Vec<WorkingGoalSummary>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkingGoalSummary {
    pub id: String,
    pub agent: String,
    pub expires_at: i64,
}
