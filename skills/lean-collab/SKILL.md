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
| `solved` | `tactic`, `solved_at` | Proof verified |
| `decomposed` | `children[]`, `strategy`, `decomposed_at` | Split into subgoals |
| `axiom` | `justification`, `axiomatized_at` | Accepted as axiom |
| `backtracked` | `attempt`, `backtracked_at` | Decomposition failed, retry |
| `exhausted` | `attempts`, `exhausted_at` | All strategies failed |
| `abandoned` | `parent_backtrack_attempt`, `abandoned_at` | Parent backtracked |

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

```
1. Start listener in background:
   ./bin/lc listen (run_in_background=true)

2. CHECK FOR WORK:
   a. ./bin/lc status
   b. If ready_to_compose → spawn composer (foreground), then DONE
   c. For each open goal → spawn agent (background)
   d. If spawn BLOCKED → skip, try next

3. WAIT FOR EVENT:
   - Check listener output for new events
   - On any event → GOTO 2 immediately
   - If no event after 5s → GOTO 2 anyway (fallback)
```

**KEEP RUNNING.** Even if all goals are "working", new goals will appear when agents finish.

**CRITICAL: NEVER read agent output files. ONLY use `./bin/lc status`.**

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
   → YOUR JUDGMENT:
     - If goal looks decomposable (compound structure) → decomposer
     - If goal looks like leaf inequality → prover

5. Otherwise → prover
```

### Quick Reference

| `has_quantifiers` | `is_numeric` | `has_transcendentals` | `state` | → Agent |
|-------------------|--------------|----------------------|---------|---------|
| — | — | — | backtracked | decomposer |
| true | — | — | open | decomposer |
| false | true | — | open | prover |
| false | false | true | open | judgment call |
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
| `./bin/lc claim <gid>` | Claim goal (hooks use this) |
| `./bin/lc unclaim <gid>` | Release goal (hooks use this) |
| `./bin/lc verify --goal <gid> --tactic <t> [--imports X,Y]` | Verify tactic (records to CI) |
| `./bin/lc axiomatize <gid> --reason <r>` | Mark as axiom |
| `./bin/lc backtrack <gid> [--reason <r>]` | Undo decomposition (records failure) |
| `./bin/lc compose [-o path]` | Build final proof |

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
