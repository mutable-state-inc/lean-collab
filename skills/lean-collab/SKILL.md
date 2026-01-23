---
name: lean-collab
description: "Collaborative theorem proving orchestrator. Uses lc CLI for state, spawns parallel agents."
---

# Lean Collaborative Proving

**YOU ARE THE ORCHESTRATOR. Keep running until proof is complete.**

## CRITICAL RULES - READ FIRST

- **Do NOT sleep or wait**
- **Do NOT investigate** errors (no --help, no reading source code)
- **Do NOT read agent output files** - use `./bin/lc status` only
- **KEEP RUNNING** until compose succeeds
- **If goals are working (not open) → KEEP WAITING** for new goals to appear

## PROOF RIGOR PHILOSOPHY

**We produce proofs that satisfy math professors. Axioms are unacceptable shortcuts.**

### Axiom Policy

| Depth | Axiom Allowed? | Action on Failure |
|-------|----------------|-------------------|
| < max_depth - 2 | **NO** | Always backtrack for better decomposition |
| >= max_depth - 2 | Only if atomic + cited | Prefer backtrack, axiom is last resort |

### What's Acceptable to Axiomatize (rare)

- `0 < Real.pi` (atomic constant, Mathlib: `Real.pi_pos`)
- `Real.sin 0 = 0` (atomic evaluation, Mathlib: `Real.sin_zero`)
- Import failures for known Mathlib lemmas (cite the lemma)

### What's NOT Acceptable to Axiomatize

- `sin x ≤ f(x)` - This is THE PROBLEM, not an axiom!
- Any inequality that requires analysis
- Anything that could be decomposed further

### Backtrack > Axiom

When a prover fails, it should backtrack to let decomposer try a different strategy. Multiple backtrack cycles are GOOD - they explore the proof space. Axioms are BAD - they leave holes.

## FIRST: Check for Existing Work

**Before doing ANYTHING else, run:**

```bash
./bin/lc init && ./bin/lc status
```

- If `open_goals` or `working_goals` exist → **Resume immediately. Go to Main Loop.**
- If `ready_to_compose` is true → **Run compose. You're done.**
- If no goals exist → Ask user for a theorem to prove.

**DO NOT ask the user what to do if there's existing work. Just resume.**

---

## Critical: Ensue-Only Coordination

**Do NOT read agent logs or output files to check progress.**

All coordination happens through Ensue:
- `./bin/lc status` → check goal states (open, working, solved, etc.)
- `./bin/lc listen` → receive real-time events when goals change

When you spawn an agent in the background, do NOT read its output file. Instead, run `./bin/lc listen` to wait for goal state changes. The agent will update Ensue when it finishes, and you'll receive the event.

---

## Setup (New Theorem Only)

**Only run this if no existing work was found above.**

**You are running from the plugin directory. The `lc` binary is at `./bin/lc`.**

```bash
./bin/lc init --create-root --theorem "<theorem statement>"
```

Output:
```json
{
  "success": true,
  "theorem_id": "putnam-2025-a2",
  "workspace": "/path/to/workspace/putnam-2025-a2",
  "ensue_url": "https://api.ensue-network.ai",
  "config": {
    "max_parallel_agents": 12,
    "max_depth": 12,
    "claim_ttl_seconds": 300
  },
  "active_subscriptions": 5
}
```

---

## Ensue Memory Structure

All persistent state lives in Ensue:

```
proofs/{theorem_id}/
├── goals/
│   └── {goal_id}       # Goal JSON object
├── solutions/
│   └── {goal_id}       # Verified tactic string
└── final-proof         # Composed Lean proof

strategies/{goal_hash}/
└── {strategy_id}       # Failed/succeeded strategy records
```

### Goal Object

Each goal at `proofs/{tid}/goals/{gid}` contains: `id`, `goal_type`, `state`, `depth`, `parent`, `hypotheses`, `has_quantifiers`, `has_transcendentals`, `is_numeric`, `strategy_attempts`, `attempt_count`.

### Goal States

| State | Fields | Meaning |
|-------|--------|---------|
| `open` | — | Available for work |
| `working` | `agent`, `claimed_at`, `expires_at` | Claimed by agent |
| `solved` | `tactic`, `imports[]`, `solved_at` | Proof verified |
| `decomposed` | `children[]`, `strategy`, `decomposed_at` | Split into subgoals |
| `axiom` | `justification`, `axiomatized_at` | Accepted as axiom |
| `backtracked` | `attempt`, `backtracked_at` | Decomposition failed, retry |
| `exhausted` | `attempts`, `exhausted_at` | All strategies failed |
| `abandoned` | `parent_backtrack_attempt`, `abandoned_at` | Goal invalidated (see below) |

**`parent_backtrack_attempt` Values:**
| Value | Meaning |
|-------|---------|
| `0` | Manual abandonment (prover called `abandon` directly) - should be rare |
| `1-N` | Cascade from parent backtrack attempt N - normal backtrack flow |
| `4294967295` (u32::MAX) | Auto-orphan cleanup (invalid ancestor detected during claim) |

**State Transitions:**
```
open ──────────┬──► working ──► solved
               │         │
               │         └──► open (claim expired)
               │
               └──► (via decomposer) decomposed ──► backtracked ──► open
                                                         │
                                          children ──► abandoned

axiom ◄── (last resort, depth >= max-2, atomic + cited)
exhausted ◄── (all strategies failed, no more options)
```

**Do NOT Spawn Agents For:**
- `abandoned` - Parent was backtracked; these goals are preserved for history only
- `exhausted` - All strategies failed; requires human intervention or proof redesign
- `solved` - Already proven
- `axiom` - Accepted as axiom
- `decomposed` - Already split into children (work on children instead)

**Cascading Invalidation:**
When a parent is backtracked, its direct children are abandoned. Grandchildren may still appear as `open`/`axiom`/etc., but the `claim` command will detect the invalid ancestor and auto-abandon them. This is lazy evaluation - descendants are cleaned up when accessed, not eagerly.

### Structural Analysis Flags

CLI detects these syntactically from `goal_type`:

| Flag | Detection |
|------|-----------|
| `has_quantifiers` | Contains `∀`, `∃`, `forall`, `exists` |
| `has_transcendentals` | Contains `Real.sin`, `Real.cos`, `Real.exp`, `Real.log`, `Real.pi`, etc. |
| `is_numeric` | Only numbers and arithmetic operators |

### Complexity (Computed)

```
is_numeric         → Trivial
has_quantifiers    → Structural
has_transcendentals → Analytical
otherwise          → Decidable
```

---

## Main Loop

**Event-driven with timeout fallback. React to events, but don't block forever.**

### Step 1: Start Listener FIRST (once only)

```bash
./bin/lc listen --prefix proofs/{theorem_id}/ --output workspace/events.jsonl
```

**Run with `run_in_background=true`.** This runs for the entire session.

### Step 2: Check Status & Spawn Agents

```bash
./bin/lc status
```

- If `ready_to_compose` → run composer, DONE
- For each `open_goals` → spawn appropriate agent (background)

### Step 3: Wait for Events (with timeout)

**Wait for new events, but don't block forever:**

```bash
timeout 45 tail -f workspace/events.jsonl
```

- **Event arrives** → go to Step 2 immediately
- **Timeout (45s)** → go to Step 2 anyway (catch anything missed)

**Events look like:**
```json
{"method":"notifications/resources/updated","params":{"uri":"memory:///proofs/.../goals/root"}}
```

### ⛔ ANTI-PATTERN (wasteful polling):

```bash
# WRONG - tight polling loop
sleep 5 && ./bin/lc status
sleep 5 && ./bin/lc status
sleep 5 && ./bin/lc status
```

### ✅ CORRECT PATTERN:

```bash
# 1. Start listener once
./bin/lc listen --prefix proofs/theorem/ --output workspace/events.jsonl &

# 2. Loop: check status → spawn → wait for events (with timeout) → repeat
while not ready_to_compose:
    ./bin/lc status → spawn agents for open_goals
    timeout 45 tail -f workspace/events.jsonl  # blocks until event OR timeout
```

**Key principle:** One status check per iteration, not one per agent. Stay active via timeout fallback.

---

## Status Commands

### Theorem Summary

```bash
./bin/lc status
```

Returns: `summary` (counts by state), `open_goals`, `working_goals`, `ready_to_compose`, `config`.

### Goal Details

```bash
./bin/lc status <goal_id>
```

Returns: `goal_type`, `state`, `depth`, `hypotheses`, `has_quantifiers`, `has_transcendentals`, `is_numeric`, `strategy_attempts`.

---

## Routing Logic

**You decide the agent type based on goal properties from `./bin/lc status`.**

### Decision Tree

```
1. state is "backtracked"?
   → decomposer (try different strategy)

2. has_quantifiers is true?
   → decomposer (needs intro/cases/constructor)

3. is_numeric is true?
   → prover (norm_num, decide)

4. has_transcendentals is true?
   → Apply TRANSCENDENTAL PHILOSOPHY (see below)

5. Otherwise → prover
```

### Transcendental Philosophy

When `has_transcendentals` is true, ask: **"Point evaluation or behavior analysis?"**

| Question | Example | Agent |
|----------|---------|-------|
| Can this be solved by evaluating at specific points? | `sin 0 = 0`, `cos π = -1`, `π > 3` | prover |
| Does this require understanding how the function behaves across a domain? | `sin x ≤ f(x)` for x ∈ [0,π], bounds requiring calculus | decomposer |

**The test:** "Does proving this require reasoning about derivatives, extrema, or function shape?"
- YES → decomposer (needs calculus setup: find critical points, analyze convexity)
- NO → prover (apply known Mathlib lemmas)

### Quick Reference

| `has_quantifiers` | `is_numeric` | `has_transcendentals` | `state` | → Agent |
|-------------------|--------------|----------------------|---------|---------|
| — | — | — | backtracked | decomposer |
| true | — | — | open | decomposer |
| false | true | — | open | prover |
| false | false | true | open | **see philosophy above** |
| false | false | false | open | prover |

---

## Spawning Agents

**Use `run_in_background=true` for parallelism.**

```
Task(
  subagent_type="lean-collab:decomposer",
  prompt="Goal ID: root\nType: ∀ x ∈ [0,π], sin x ≤ f(x)",
  run_in_background=true
)
```

```
Task(
  subagent_type="lean-collab:lean-prover",
  prompt="Goal ID: membership\nType: 0 < 18",
  run_in_background=true
)
```

**Spawn multiple in ONE message for parallelism.**

---

## Events

```bash
./bin/lc listen
```

Outputs JSON lines:
```json
{"event":"goal_updated","key":"proofs/test/goals/root","goal_id":"root"}
```

---

## Composition

When `ready_to_compose` is true:

```bash
./bin/lc compose
```

**Output:** Writes verified proof to `workspace/{theorem_id}/output/proof.lean`

Tell the user the file path when complete so they can access it.

---

## CLI Reference

| Command | Purpose |
|---------|---------|
| `./bin/lc init --create-root --theorem "..."` | Setup + create root goal |
| `./bin/lc status` | Theorem summary with open/working goals |
| `./bin/lc status <gid>` | Full goal details |
| `./bin/lc create-goal --id X --type T --depth D` | Create goal (auto-subscribes) |
| `./bin/lc decompose <gid> --children X,Y --strategy S` | Mark goal as decomposed |
| `./bin/lc search "query" --prefix tactics/` | Search collective intelligence |
| `./bin/lc listen` | SSE event stream |
| `./bin/lc claim <gid>` | Claim goal (**checks ancestors**, auto-abandons if invalid) |
| `./bin/lc unclaim <gid>` | Release goal (hooks use this) |
| `./bin/lc verify --goal <gid> --tactic <t> [--imports X,Y]` | Verify tactic (**returns Lean errors in `error` field**) |
| `./bin/lc axiomatize <gid> --reason <r> [--force]` | Mark as axiom (**REFUSES invalid reasons/depth**) |
| `./bin/lc backtrack <gid> [--reason <r>]` | Undo decomposition, abandon children |
| `./bin/lc abandon <gid> [--reason <r>]` | Abandon goal (**auto-backtracks parent** for leaf goals) |
| `./bin/lc compose [-o path]` | Build final proof |

### CLI Validation (Enforced Automatically)

**`abandon` auto-backtracks:**
- For goals with a parent → CLI calls backtrack on parent instead
- Parent goes to `Backtracked` state, children cascade-abandoned
- Use `--force` to bypass (for cleanup only)
- Root goals (no parent) are directly abandoned

**`axiomatize` REFUSES if:**
- `depth < max_depth - 2` (must decompose further)
- Reason contains: "false", "impossible", "scaffold", "syntax", "bug"
- Goal has quantifiers (should decompose)
- Use `--force` to override (logged as warning)

**`claim` checks ancestors:**
- Walks up parent chain before claiming
- If ANY ancestor is `abandoned` or `backtracked` → auto-abandons the goal
- Returns `{"error": "invalid_ancestor", "action_taken": "auto_abandoned"}`

**`verify` error handling:**
- Lean errors now appear in `error` field (fixed bug where errors went to stdout only)
- Check `error` field to understand WHY tactics fail

## Collective Intelligence

Successful tactics and failed strategies are recorded:

```
tactics/solutions/{hash}-{ts}    # Successful proofs (from ./bin/lc verify)
strategies/{hash}/{strategy}-{ts} # Failed decompositions (from ./bin/lc backtrack)
```

**Different agents use this differently:**

### Prover → Searches for proven tactics to adapt
```bash
./bin/lc search "numeric conjunction" --prefix tactics/solutions/
```
Finds tactics that worked on similar goals. Adapts the reasoning to the current goal.

### Decomposer → Reads failed strategies from goal status
```bash
./bin/lc status $GOAL_ID
# Returns strategy_attempts[] with error reasons
```
When a goal is backtracked, the decomposer reads `strategy_attempts` to understand WHY previous decompositions failed, then tries a different approach. The error message guides the next attempt.

---

## Strategy History

For backtracked goals, check `./bin/lc status <gid>` for `strategy_attempts` array. Include failed strategies in decomposer prompt so it tries a different approach.

---

## Config Override

Environment variables override `.lean-collab.json`:

```bash
export LEAN_COLLAB_MAX_PARALLEL_AGENTS=6
export LEAN_COLLAB_MAX_DEPTH=8
export LEAN_COLLAB_CLAIM_TTL=600
```
