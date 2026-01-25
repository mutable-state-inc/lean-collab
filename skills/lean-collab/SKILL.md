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

## CORE PHILOSOPHY: THINK FIRST, COMPILE SECOND

**We combine the LLM's mathematical reasoning with Lean's verification to avoid wasted attempts.**

### The Problem We Solved

The old suggest-first approach fails for complex goals:
- `suggest` only finds direct lemma applications
- Module arithmetic, geometry, abstract types have no single-lemma solutions
- Guessing 10 tactics wastes verification cycles

### The Solution: LLM Intelligence + Lean Verification

| What LLMs Do Best | What Lean Does Best |
|-------------------|---------------------|
| Proof architecture design | Type checking |
| Creative strategies | Finding direct lemmas |
| Understanding math concepts | Verification |
| Multi-step reasoning | Detecting sorry/errors |

**Workflow:**
1. **LLM THINKS** about the math (MATH CARD / ARCHITECTURE CARD)
2. **LLM DESIGNS** the proof skeleton with `sorry` placeholders
3. **Lean VALIDATES** the skeleton compiles (`--skeleton` flag)
4. **Only then** create subgoals or verify final tactics

### Skeleton Verification (NEW)

Before decomposing, validate your architecture compiles:

```bash
./bin/lc verify --goal $GOAL_ID --tactic "have h1 : <subgoal1> := sorry; have h2 : <subgoal2> := sorry; <final_step>" --skeleton
```

If skeleton fails → try different architecture BEFORE creating subgoals.
If skeleton passes → safe to decompose.

### Reasoning Cards (Required for Complex Goals)

**MATH CARD (Prover - for complex tactics):**
```
┌─MATH─────────────────────────────────────────┐
│ GOAL: <the goal>                              │
├──────────────────────────────────────────────┤
│ CLASS: <arith/analytical/geometric/etc>       │
│ KEY:   <core mathematical insight>            │
│ WHY:   <why this insight applies>             │
├──────────────────────────────────────────────┤
│ TACTICS: <candidate tactics based on insight> │
│ PATTERN: <Lean pattern to follow>             │
└──────────────────────────────────────────────┘
```

**ARCHITECTURE CARD (Decomposer - before creating subgoals):**
```
┌─ARCHITECTURE────────────────────────────────────────┐
│ GOAL: <the goal>                                     │
│ PROOF IDEA: <1-2 sentence description>               │
│ KEY INSIGHT: <what mathematical fact makes this work>│
│ SUBGOALS:                                            │
│   1. <subgoal1> - because: <why needed>              │
│   2. <subgoal2> - because: <why needed>              │
│ ASSEMBLY: <how subgoals combine>                     │
│ LEAN SKETCH: have h1 := sorry; have h2 := sorry; ... │
│ POTENTIAL ISSUES: <circular deps? missing hyps?>     │
└──────────────────────────────────────────────────────┘
```

---

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
./bin/lc init --create-root \
  --theorem "<theorem goal statement>" \
  --hypotheses "<hyp1>;;hyp2;;..."
```

**CRITICAL:** The `--hypotheses` flag is required for theorems with assumptions. Without it, child goals won't have access to the theorem's hypotheses and proofs will fail.

Example for Putnam B1:
```bash
./bin/lc init --create-root \
  --theorem "∃ c : Bool, ∀ P : EuclideanSpace ℝ (Fin 2), color P = c" \
  --hypotheses "color : EuclideanSpace ℝ (Fin 2) → Bool;;h : ∀ (s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2), (∀ i j : Fin 3, color (s.points i) = color (s.points j)) → color s.circumcenter = color (s.points 0)"
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
is_numeric          → Trivial         (prover: norm_num, decide)
has_quantifiers     → Structural      (decomposer: intro, cases)
has_transcendentals → Analytical      (decomposer: calculus setup)
otherwise           → NeedsJudgment   (YOU MUST CLASSIFY - see below)
```

### Classifying NeedsJudgment Complexity

When `complexity: "needs_judgment"`, **YOU must analyze the goal** before spawning. Don't guess - think:

```
┌─CLASSIFY────────────────────────────────────────┐
│ GOAL: <goal_type>                                │
│ HYPOTHESES: <list them>                          │
├──────────────────────────────────────────────────┤
│ Q1: Can any hypothesis directly prove this?      │
│ Q2: Do I need to CONSTRUCT something first?      │
│ Q3: Is this a single tactic or multi-step?       │
├──────────────────────────────────────────────────┤
│ VERDICT: SIMPLE → prover | COMPLEX → decomposer  │
└──────────────────────────────────────────────────┘
```

**Examples:**

| Goal | Hypotheses | Verdict | Why |
|------|------------|---------|-----|
| `2 + 2 = 4` | none | SIMPLE | arithmetic |
| `color P = color 0` | `h : monochromatic simplex → ...` | COMPLEX | need to construct simplices |
| `x ∈ S` | `hx : x ∈ S` | SIMPLE | direct hypothesis |
| `P ∧ Q` | `hP : P`, `hQ : Q` | SIMPLE | constructor with both available |
| `f x = g x` | `h : ∀ y, f y = g y` | SIMPLE | direct apply |
| `dist A B = dist C D` | geometric setup | COMPLEX | likely needs construction |

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

2. complexity is "needs_judgment"?
   → Check DEPTH first:
     a) depth >= 3 → prover FIRST (try ≥3 tactics before giving up)
     b) depth < 3  → YOU CLASSIFY (see below)
   → At deeper depths, goals are likely leaves that just need the right tactic
   → At shallow depths, goals often need decomposition

3. can_decompose is TRUE and complexity is NOT needs_judgment?
   → decomposer (goal needs to be split)

4. can_decompose is FALSE?
   → prover (goal is a leaf, try tactics)
```

**The CLI computes `can_decompose` based on:**
- Depth limit (can't decompose at max depth)
- Complexity (structural/analytical/needs_judgment → can decompose)
- Quantifiers (∀/∃ → needs intro/cases)

**IMPORTANT:** When `complexity: "needs_judgment"`:
- **At depth ≥ 3:** Send to prover first. These are likely provable leaves. The prover MUST try at least 3 different tactics before abandoning.
- **At depth < 3:** Use your judgment with the CLASSIFY card. Shallow goals often need decomposition.

This prevents the failure mode where agents decompose endlessly without ever trying to prove anything.

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

| `state` | `complexity` | `depth` | → Agent |
|---------|--------------|---------|---------|
| backtracked | — | — | decomposer |
| open/working | `needs_judgment` | ≥ 3 | **prover** (try ≥3 tactics first) |
| open/working | `needs_judgment` | < 3 | **YOU CLASSIFY** → likely decomposer |
| open/working | structural/analytical | — | decomposer |
| open/working | trivial | — | prover |

**When `complexity: "needs_judgment"` at depth ≥ 3:** Send to prover. Don't overthink it - deeper goals are usually leaves that need the right tactic found.

**When `complexity: "needs_judgment"` at depth < 3:** Use the CLASSIFY card. Shallow goals often need decomposition before proving.

---

## Spawning Agents

**Use `run_in_background=true` for parallelism.**

### Decomposer Spawn

```
Task(
  subagent_type="lean-collab:decomposer",
  prompt="Goal ID: root\nType: ∀ x ∈ [0,π], sin x ≤ f(x)",
  run_in_background=true
)
```

### Prover Spawn

**Just pass goal context. The prover agent has REPL exploration instructions.**

```
Task(
  subagent_type="lean-collab:lean-prover",
  prompt="Goal ID: <id>
Goal: <goal_type>
Hypotheses:
<hyp1>
<hyp2>
...",
  run_in_background=true
)
```

The prover will:
1. Think about the math approach
2. Use `./bin/lc explore` to test tactics and see remaining goals
3. Iterate based on Lean feedback
4. Verify when complete or abandon if stuck

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
| `./bin/lc init --create-root --theorem "..." --hypotheses "..."` | Setup + create root goal with hypotheses |
| `./bin/lc status` | Theorem summary with open/working goals |
| `./bin/lc status <gid>` | Full goal details |
| `./bin/lc create-goal --id X --goal-type T --depth D` | Create goal (auto-subscribes, **checks for duplicates**) |
| `./bin/lc decompose <gid> --children X,Y --strategy S` | Mark goal as decomposed |
| `./bin/lc search "query" --prefix tactics/` | Search collective intelligence |
| `./bin/lc listen` | SSE event stream |
| `./bin/lc claim <gid>` | Claim goal (**checks ancestors**, auto-abandons if invalid) |
| `./bin/lc unclaim <gid>` | Release goal (hooks use this) |
| `./bin/lc verify --goal <gid> --tactic <t> [--imports X,Y] [--skeleton]` | Verify tactic (**`--skeleton` allows sorry for architecture validation**) |
| `./bin/lc axiomatize <gid> --reason <r> [--force]` | Mark as axiom (**REFUSES invalid reasons/depth**) |
| `./bin/lc backtrack <gid> [--reason <r>]` | Undo decomposition, abandon children |
| `./bin/lc abandon <gid> [--reason <r>]` | Abandon goal (**auto-backtracks parent** for leaf goals) |
| `./bin/lc compose [-o path]` | Build final proof |

### CLI Validation (Enforced Automatically)

**`create-goal` checks for duplicates/circular decompositions (NEW):**
- Uses embeddings to find similar existing goals
- **Blocks** if similarity > 92% (likely duplicate or circular)
- **Warns** if similarity > 85% (suspicious)
- Detects circular decompositions (child goal equivalent to ancestor)
- Use `--check-similar=false` to disable (not recommended)

**`abandon` does NOT cascade:**
- Abandoning a goal only affects that goal
- Siblings continue working independently
- Parent stays in `decomposed` state
- Use `./bin/lc backtrack <parent>` to abandon entire decomposition strategy

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
