---
name: lean-collab
description: "Collaborative theorem proving orchestrator. Spawns parallel agents, watches for state changes, continues until proof complete."
---

# LeanTree Collaborative Proving

**YOU ARE THE ORCHESTRATOR. Keep running until proof is complete.**

Multiple agents work in parallel, share state via Ensue, and contribute to collective intelligence.

---

## ⚙️ Concurrency Control

Add `max_parallel_agents` to `.lean-collab.json` to limit CPU usage:

```json
{
  "theorem_id": "putnam-2025-a2",
  "plugin_path": "/path/to/plugin",
  "max_parallel_agents": 3
}
```

**Default: 9.** Lower this (e.g., 3) if your machine overheats. The skill will queue excess goals and spawn new agents as slots free up.

---

## ⚡ EXECUTE THIS LOOP (Don't Just Read - DO IT)

```
1. INIT:     eval $("$PLUGIN/scripts/init-session.sh" --export)
2. CHECK:    ACTION=$("$SCRIPTS/next-action.sh" "$TID")
3. HANDLE:   claim   → CLAIM goals, spawn agents (background), --wait, GOTO 2
             wait    → block with --wait, GOTO 2
             compose → SPAWN lean-composer agent, DONE
             error   → report and stop
```

**⚠️ CLAIM BEFORE SPAWN:** Run `claim-goal.sh` for each goal BEFORE spawning its agent.

**⚠️ COMPOSE IS NOT OPTIONAL:** When you get `action=compose`, you MUST spawn the lean-composer agent:
```
Task(subagent_type="lean-collab:lean-composer", prompt="STATE_DIR=$STATE_DIR. Compose proof for $TID.")
```

**Keep looping until compose or error. Don't stop after spawning agents - wait for notifications!**

---

## ⛔ THERE IS NO `ensue` COMMAND

**These do NOT exist - do NOT try them:**
- ❌ `ensue` - no such command
- ❌ `ensue get_memory` - does not exist
- ❌ `ensue --path` - does not exist
- ❌ `ensue_get`, `ensue_list` - do not exist

**The ONLY way to call the API is via the `$E` variable (set by init-session.sh):**
```bash
$E get_memory '{"key_names":["proofs/my-theorem/goals/root/status"]}'
```

`$E` points to a shell script (`ensue-api.sh`) that wraps curl. It is NOT a binary.

---

## 🚀 QUICK START (Read This First!)

**Your workflow is simple:**

```bash
# 1. Initialize (once per session)
PLUGIN=$(cat .lean-collab.json | jq -r '.plugin_path')
eval $("$PLUGIN/scripts/init-session.sh" --export)
# Now you have: E, TID, SCRIPTS, SID, STATE_DIR, LEAN_PROJECT, MAX_DEPTH

# 2. Check what to do
ACTION=$("$SCRIPTS/next-action.sh" "$TID")
echo "$ACTION"
# Returns: {"action":"claim","goals":["root"]} or {"action":"compose"} or {"action":"wait"}

# 3. Act on it
WHAT=$(echo "$ACTION" | jq -r '.action')
case "$WHAT" in
    claim)  # Claim goals and spawn agents IN BACKGROUND
        GOALS=$(echo "$ACTION" | jq -r '.goals[]')
        for GOAL_ID in $GOALS; do
            "$SCRIPTS/claim-goal.sh" "$TID" "$GOAL_ID" "skill" "$SID" || continue
            # Spawn with run_in_background=true (see Claiming section)
        done
        # After spawning, wait for notifications
        ACTION=$("$SCRIPTS/next-action.sh" "$TID" --wait)
        ;;
    compose)  # All done - MUST spawn composer agent!
        # ⚠️ DO NOT SKIP THIS - spawn the composer:
        # Task(subagent_type="lean-collab:lean-composer", prompt="STATE_DIR=$STATE_DIR. Compose proof for $TID.")
        exit 0  # Done after spawning composer
        ;;
    wait)  # Block until something changes
        ACTION=$("$SCRIPTS/next-action.sh" "$TID" --wait)
        # Then handle the new action
        ;;
esac
# LOOP BACK to check ACTION again!
```

**Key points:**
1. Spawn agents with `run_in_background=true` for parallelism
2. After spawning, use `--wait` to block until SSE notification
3. Keep looping until `compose` action

---

## ⛔ FORBIDDEN PATTERNS

```bash
# ❌ NEVER DO THESE:
sleep 5 && $E get_memory ...     # Polling loop - FORBIDDEN
sleep 10 && check ...            # Polling loop - FORBIDDEN
while true; do sleep...; done    # Polling loop - FORBIDDEN

# ✅ ALWAYS USE:
"$SCRIPTS/next-action.sh" "$TID" --wait   # Event-driven blocking
```

---

## Available Scripts

| Script | Purpose | Usage |
|--------|---------|-------|
| `init-session.sh` | Create isolated state dir | `eval $("$SCRIPTS/init-session.sh" --export)` |
| `load-session.sh` | Load state (for subagents) | `eval $("$SCRIPTS/load-session.sh" $STATE_DIR)` |
| `next-action.sh` | What should I do? | `$SCRIPTS/next-action.sh $TID` |
| `next-action.sh --wait` | Block until work available | `$SCRIPTS/next-action.sh $TID --wait` |
| `find-open-goals.sh` | List claimable goal IDs | `$SCRIPTS/find-open-goals.sh $TID` |
| `claim-goal.sh` | Claim with verification | `$SCRIPTS/claim-goal.sh $TID $GOAL_ID agent $SID` |
| `route-goal.sh` | **MANDATORY** routing | `$SCRIPTS/route-goal.sh $TID $GOAL_ID` → "decomposer" or "prover" |
| `compose-proof.sh` | Compose final proof | `$SCRIPTS/compose-proof.sh $TID` |

---

## Ensue API Reference

**All calls use `$E` (set by init-session.sh):**

| Method | Usage |
|--------|-------|
| `get_memory` | `$E get_memory '{"key_names":["proofs/'"$TID"'/goals/root/status"]}'` |
| `list_keys` | `$E list_keys '{"prefix":"proofs/'"$TID"'/goals/","limit":50}'` |
| `create_memory` | `$E create_memory '{"items":[{"key_name":"...","value":"...","embed":true}]}'` |
| `update_memory` | `$E update_memory '{"key_name":"...","value":"..."}'` |
| `delete_memory` | `$E delete_memory '{"key_names":["key1","key2"]}'` |
| `search_memories` | `$E search_memories '{"query":"...","prefix":"...","limit":5}'` |
| `subscribe_to_memory` | `$E subscribe_to_memory '{"key_name":"..."}'` |

**Parse responses with jq:**
```bash
$E get_memory '{"key_names":["proofs/'"$TID"'/goals/root/status"]}' | jq -r '.result.structuredContent.results[0].value // empty'
```

---

## Full Workflow

### Step 1: Initialize Session

```bash
PLUGIN=$(cat .lean-collab.json | jq -r '.plugin_path')
eval $("$PLUGIN/scripts/init-session.sh" --export)
# Now you have: STATE_DIR, E, TID, SCRIPTS, SID, LEAN_PROJECT, MAX_DEPTH
```

### Step 2: Orchestration Loop (KEEP RUNNING)

**After each action, IMMEDIATELY check for more work. Don't stop.**

```bash
# Check what to do
ACTION=$("$SCRIPTS/next-action.sh" "$TID")
WHAT=$(echo "$ACTION" | jq -r '.action')
```

**Handle based on action:**

| Action | What to do | Then |
|--------|------------|------|
| `claim` | Claim goals, spawn agents with `run_in_background=true` | → `--wait` for notifications |
| `wait` | `"$SCRIPTS/next-action.sh" "$TID" --wait` | → Handle new action |
| `compose` | **MUST** spawn `lean-composer` agent | → DONE |
| `error` | Report error | → Stop |

**⚠️ CRITICAL:**
- After spawning background agents, use `--wait` to block until they finish (via SSE)
- When `action=compose`, you MUST spawn the composer - don't skip this step!

### Step 3: Claiming and Spawning Agents

**⚠️ CRITICAL: CLAIM BEFORE SPAWNING, TRACK SPAWNS TO PREVENT OOM**

For each goal in the claim list:

```bash
# 1. CLAIM FIRST (atomic - prevents race)
if "$SCRIPTS/claim-goal.sh" "$TID" "$GOAL_ID" "skill" "$SID"; then
    # 2. USE route-goal.sh TO DECIDE AGENT TYPE (MANDATORY!)
    AGENT_TYPE=$("$SCRIPTS/route-goal.sh" "$TID" "$GOAL_ID")
    # 3. TRACK SPAWN (prevents thundering herd - CRITICAL!)
    "$SCRIPTS/spawn-track.sh" start "$STATE_DIR"
    # 4. THEN spawn the correct agent based on routing
fi
```

**⚠️ MANDATORY: Use `route-goal.sh` for ALL routing decisions!**
```bash
AGENT_TYPE=$("$SCRIPTS/route-goal.sh" "$TID" "$GOAL_ID")
# Returns: "decomposer" or "prover"
```

**DO NOT try to guess the agent type yourself. The script checks:**
1. If goal has `∀`, `∃`, `→` → decomposer (need intro)
2. If goal has no quantifiers → prover (prove or axiomatize)

**Spawn the appropriate agent IN BACKGROUND:**
```
if [ "$AGENT_TYPE" = "decomposer" ]; then
    Task(subagent_type="lean-collab:decomposer", prompt="STATE_DIR=$STATE_DIR. Decompose goal $GOAL_ID.", run_in_background=true)
else
    Task(subagent_type="lean-collab:lean-prover", prompt="STATE_DIR=$STATE_DIR. Prove goal $GOAL_ID.", run_in_background=true)
fi
```

**⚠️ CRITICAL: Use `run_in_background=true` for ALL agent spawns!**
- This enables true parallelism - multiple agents work simultaneously
- Don't wait for agents to finish - they update Ensue when done
- SSE notifications will trigger `next-action.sh --wait` to unblock

**For multiple goals:** Claim all first, then spawn all agents in ONE message with `run_in_background=true`.

**⚠️ After spawning, IMMEDIATELY go back to Step 2 to check for more work (or --wait).**

---

## Decision Tree (When to Decompose vs Prove)

**⚠️ USE $MAX_DEPTH FROM INIT (exported by init-session.sh).**
Example: If config has `max_depth: 35`, then `$MAX_DEPTH=35`.
- Depth 5 with MAX_DEPTH=35 is SHALLOW (14%)
- Depth 5 with MAX_DEPTH=8 is DEEP (62%)

```
┌─────────────────────────────────────────────────────────────┐
│  For each open goal from next-action.sh:                     │
│  USE $MAX_DEPTH (e.g., 35) NOT a hardcoded value!            │
│                                                              │
│  0. CHECK DEPTH FIRST (get from goals/{id}/depth)            │
│     ├── depth >= $MAX_DEPTH → PROVER (must prove, no decomp) │
│     └── depth < $MAX_DEPTH → continue                        │
│                                                              │
│  1. ⚠️ QUANTIFIER CHECK FIRST (always decompose these!)      │
│     Does goal type contain ∀, ∃, →, forall, exists?          │
│     ├── YES → DECOMPOSER (intro needed, regardless of hints) │
│     └── NO  → continue                                       │
│                                                              │
│  2. Does goal have leaf_type set?                            │
│     ├── YES → PROVER (decomposer marked it as leaf)          │
│     └── NO  → continue                                       │
│                                                              │
│  3. Is it pure decidable arithmetic?                         │
│     (no variables, no transcendentals)                       │
│     ├── YES → PROVER (norm_num, native_decide)               │
│     └── NO  → continue                                       │
│                                                              │
│  4. Does goal involve transcendental functions?              │
│     (Real.sin, Real.cos, Real.exp, Real.log, Real.pi, etc.)  │
│     ├── YES and depth < $MAX_DEPTH - 3 → DECOMPOSER          │
│     │   (e.g., MAX_DEPTH=35: depth < 32 → DECOMPOSER)        │
│     ├── YES and depth >= $MAX_DEPTH - 3 → PROVER             │
│     └── NO  → PROVER                                         │
│                                                              │
│  5. AXIOM FALLBACK (when prover fails on hard goals)         │
│     Prover attempts 3 tactics, all fail:                     │
│     ├── Goal is FALSE → error:malformed_goal                 │
│     ├── Goal depth < MAX_DEPTH-1 → needs_decomposition       │
│     │   (TOO SHALLOW for axiom - must decompose further!)    │
│     ├── Goal depth >= MAX_DEPTH-1 AND TRUE → axiom           │
│     └── Goal might decompose better → needs_decomposition    │
│                                                              │
│  When in doubt at shallow depth → DECOMPOSER                 │
│  When in doubt at deep depth → PROVER (can axiomatize)       │
└─────────────────────────────────────────────────────────────┘
```

**⚠️ CRITICAL: Step 1 (quantifiers) MUST come before step 2 (leaf_type).**
A goal with `leaf_type=discoverable` but `∀ x, ...` in its type still needs `intro` first!

**Transcendental function heuristic:**
Inequalities involving sin, cos, exp, log, pi are rarely directly provable.
Decompose them by:
- Splitting into sub-intervals (e.g., [0, π/2] vs [π/2, π])
- Using known bounds (sin x ≤ x, cos x ≤ 1 - x²/2 + x⁴/24)
- Transforming via identities (sin(π-x) = sin(x))

**Axiom-worthy goals (TRUE but hard to prove formally):**
- `sin x ≤ (4/π²)·x·(π-x)` - parabola bounds sin
- `arcsin x ≥ x + x³/6` - Taylor lower bound
- `π² < 10` - numerical bound
- Any well-known inequality from analysis textbooks

**Depth-based routing (relative to $MAX_DEPTH):**
- Shallow (< 30% of MAX_DEPTH): Decompose freely
- Mid (30-70% of MAX_DEPTH): Balance decomposition and proving
- Deep (> 70% of MAX_DEPTH): Bias toward proving

Example with MAX_DEPTH=35: shallow=0-10, mid=11-24, deep=25+

---

## Subscription & Notification System

**How collaborative waiting works (no polling!):**

```
┌─────────────────────────────────────────────────────────────┐
│  1. init-session.sh:                                         │
│     - Starts listener.sh (SSE connection to Ensue)           │
│     - Calls refresh-subscriptions.sh for existing goals      │
│     - Writes notifications to $STATE_DIR/notifications.log   │
│                                                              │
│  2. When agent creates new goals:                            │
│     - Agent calls refresh-subscriptions.sh                   │
│     - New goal keys get subscribed                           │
│                                                              │
│  3. When agent updates state (solved, decomposed):           │
│     - Ensue sends notification via SSE                       │
│     - listener.sh writes to notifications.log                │
│                                                              │
│  4. next-action.sh --wait:                                   │
│     - Watches notifications.log for changes                  │
│     - Unblocks when notification arrives                     │
│     - Returns new action based on updated state              │
└─────────────────────────────────────────────────────────────┘
```

**Key scripts:**
- `listener.sh` - SSE connection, writes to notifications.log
- `refresh-subscriptions.sh` - Subscribes to goal status/solution keys
- `next-action.sh --wait` - Blocks until notification, then returns action

**Agents must call `refresh-subscriptions.sh` after creating new goals!**

---

## Ensue Namespace

```
proofs/{theorem-id}/
├── _meta/
│   ├── theorem         # Original theorem statement
│   ├── status          # active | solved
│   └── goal_index      # List of all goal IDs
│
├── goals/
│   └── {goal-id}/
│       ├── definition  # {"type":"...", "hypotheses":[...]}
│       ├── status      # open | working:{agent}:{ts} | decomposed | solved
│       ├── parent      # Parent goal-id
│       ├── children    # Child goal-ids (if decomposed)
│       ├── depth       # Depth in tree (root=0, children=parent+1)
│       ├── tactic      # Tactic used to decompose
│       └── leaf_type   # decidable | discoverable | algebraic
│
├── solutions/
│   └── {goal-id}       # Verified tactic that solved this leaf
│
├── attempts/
│   └── {goal-id}/
│       └── {hash}      # Failed tactic + error
│
└── final-proof         # Composed complete proof
```

---

## Goal States

| Status | Meaning |
|--------|---------|
| `open` | Available to claim |
| `working:{agent}:{timestamp}` | Claimed by agent |
| `decomposed` | Has children, not a leaf |
| `solved` | Leaf goal verified |
| `axiom` | Goal accepted as axiom (generates `axiom` declaration) |
| `solved_by_axiom:{ref}` | Goal proved by referencing an axiom |
| `needs_decomposition` | Prover gave up |
| `error:malformed_goal` | Goal is mathematically false |

---

## Axioms

**⚠️ DEPTH RESTRICTION: Axioms are ONLY allowed in deep regions of the proof tree.**

A mathematician won't accept axioms for high-level goals. Only leaf-level lemmas can be axiomatized.

**Minimum depth for axioms:** `depth >= MAX_DEPTH - 1`

| MAX_DEPTH | MIN_AXIOM_DEPTH | Meaning |
|-----------|-----------------|---------|
| 3 | 2 | Only depth 2+ goals can be axioms |
| 4 | 3 | Only depth 3+ goals can be axioms |
| 5 | 4 | Only depth 4+ goals can be axioms |

**When to use axioms (IF deep enough):**
- Goal is mathematically TRUE but too hard to prove formally
- Goal requires analysis beyond Lean's automation (transcendental inequalities)
- Goal is a well-known result that would take too long to formalize

**When NOT to use axioms:**
- Goal is at a shallow depth (decompose instead!)
- Goal might be FALSE (mark as `error:malformed_goal`)
- Goal could be decomposed further

**How to mark a goal as axiom (prover checks depth first):**
```bash
# Check depth before axiomatizing!
GOAL_DEF=$($E get_memory '{"key_names":["proofs/'$TID'/goals/'$GOAL_ID'/definition"]}' | jq -r '.result.structuredContent.results[0].value')
GOAL_DEPTH=$(echo "$GOAL_DEF" | jq -r '.depth // 0')
MIN_AXIOM_DEPTH=$((MAX_DEPTH - 1))

if [ "$GOAL_DEPTH" -ge "$MIN_AXIOM_DEPTH" ]; then
  # Deep enough - can axiomatize
  $E update_memory '{"key_name":"proofs/'$TID'/goals/'$GOAL_ID'/status","value":"axiom"}'
else
  # Too shallow - must decompose instead
  $E update_memory '{"key_name":"proofs/'$TID'/goals/'$GOAL_ID'/status","value":"needs_decomposition"}'
fi
```

**How to reference a library axiom:**
```bash
# First, create the axiom in the library
$E create_memory '{"items":[{
  "key_name":"axioms/sin-below-parabola",
  "value":"axiom sin_below_parabola : ∀ x ∈ Set.Icc 0 Real.pi, Real.sin x ≤ (4/Real.pi^2) * x * (Real.pi - x)",
  "description":"sin lies below parabola",
  "embed":true
}]}'

# Then mark goal as solved by that axiom
$E update_memory '{"key_name":"proofs/'$TID'/goals/'$GOAL_ID'/status","value":"solved_by_axiom:axioms/sin-below-parabola"}'
```

**Fixing bad decompositions:**
If a goal was decomposed incorrectly (children are malformed):
```bash
# 1. Reset parent to open
$E update_memory '{"key_name":"proofs/'$TID'/goals/'$PARENT_ID'/status","value":"open"}'

# 2. Clear decomposition metadata
$E delete_memory '{"key_names":[
  "proofs/'$TID'/goals/'$PARENT_ID'/children",
  "proofs/'$TID'/goals/'$PARENT_ID'/tactic"
]}'

# 3. Mark bad children as errors (they'll be skipped by composer)
for CHILD in bad-child-1 bad-child-2; do
  $E update_memory '{"key_name":"proofs/'$TID'/goals/'$CHILD'/status","value":"error:malformed_goal"}'
done
```

---

## Leaf Detection

**A goal is a TRUE LEAF only if:**
1. Has no children
2. Contains NO quantifiers: `∀`, `∃`
3. Contains NO implications: `→`
4. Is decidable/computable

**Examples:**
- `0 < 18` → TRUE LEAF
- `18 * 19 > 2023` → TRUE LEAF
- `∀ x ∈ [0,π], f(x) ≤ g(x)` → NOT A LEAF (needs intro)
- `x * (1 - x) ≤ 1/4` with hypotheses → Check if decidable

---

## Named Violations

| Violation | Pattern | Fix |
|-----------|---------|-----|
| **POLL-LOOP** | `sleep N && get_memory` | Use `next-action.sh --wait` |
| **CLAIM-STEAL** | Spawning for `working:*` goal | Use `find-open-goals.sh` |

---

## If You Get Blocked

When the hook says:
```
BLOCKED: Goal 'X' already claimed!
Current status: working:skill-xK9mP2nQ:1234567
```

**Correct action:**
1. Don't rationalize - it's NOT your claim
2. Use `next-action.sh` to find OTHER work
3. Or use `next-action.sh --wait` to block until something changes

---

## Composition

When `next-action.sh` returns `{"action":"compose"}`:

**Option 1: Spawn composer agent (recommended)**
```
Task(subagent_type="lean-collab:lean-composer", prompt="STATE_DIR=$STATE_DIR. Compose and verify proof for theorem $TID.", run_in_background=true)
```

The composer agent will:
1. Run `compose-proof.sh` to build the proof tree
2. Verify with `lake env lean`
3. Check for `sorry`
4. Update Ensue with final proof
5. Write local `.lean` file

**Option 2: Direct script call**
```bash
"$SCRIPTS/compose-proof.sh" "$TID"
```

This recursively combines solutions into the final proof (but doesn't verify).
