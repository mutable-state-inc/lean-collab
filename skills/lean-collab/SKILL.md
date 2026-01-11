---
name: lean-collab
description: "Collaborative theorem proving orchestrator. Spawns parallel agents, watches for state changes, continues until proof complete."
---

# LeanTree Collaborative Proving

**YOU ARE THE ORCHESTRATOR. Keep running until proof is complete.**

Multiple agents work in parallel, share state via Ensue, and contribute to collective intelligence.

---

## ⚡ EXECUTE THIS LOOP (Don't Just Read - DO IT)

```
1. INIT:     eval $("$PLUGIN/scripts/init-session.sh" --export)
2. CHECK:    ACTION=$("$SCRIPTS/next-action.sh" "$TID")
3. HANDLE:   claim → CLAIM goals first, THEN spawn agents, GOTO 2
             wait  → block with --wait, then GOTO 2
             compose → run compose-proof.sh, DONE
             error → report and stop
```

**⚠️ CLAIM BEFORE SPAWN:** Run `claim-goal.sh` for each goal BEFORE spawning its agent. This prevents race conditions.

**Keep looping until compose or error. Don't stop after spawning one agent.**

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
# Now you have: E, TID, SCRIPTS, SID, STATE_DIR

# 2. Check what to do
ACTION=$("$SCRIPTS/next-action.sh" "$TID")
echo "$ACTION"
# Returns: {"action":"claim","goals":["root"]} or {"action":"compose"} or {"action":"wait"}

# 3. Act on it
WHAT=$(echo "$ACTION" | jq -r '.action')
case "$WHAT" in
    claim)  # Claim goals and spawn agents
        GOALS=$(echo "$ACTION" | jq -r '.goals[]')
        for GID in $GOALS; do
            # Claim and spawn (see Claiming section)
        done
        ;;
    compose)  # All done - compose final proof
        "$SCRIPTS/compose-proof.sh" "$TID"
        ;;
    wait)  # Block until something changes
        ACTION=$("$SCRIPTS/next-action.sh" "$TID" --wait)
        # Then handle the new action
        ;;
esac
```

**That's it.** The scripts handle subscriptions, notifications, and state checking.

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
| `claim-goal.sh` | Claim with verification | `$SCRIPTS/claim-goal.sh $TID $GID agent $SID` |
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
# Now you have: STATE_DIR, E, TID, SCRIPTS, SID
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
| `claim` | Spawn agents for each goal (in parallel) | → Check again |
| `wait` | `"$SCRIPTS/next-action.sh" "$TID" --wait` | → Handle new action |
| `compose` | `"$SCRIPTS/compose-proof.sh" "$TID"` | → DONE |
| `error` | Report error | → Stop |

### Step 3: Claiming and Spawning Agents

**⚠️ CRITICAL: CLAIM BEFORE SPAWNING**

For each goal in the claim list:

```bash
# 1. CLAIM FIRST (atomic - prevents race)
if "$SCRIPTS/claim-goal.sh" "$TID" "$GID" "skill" "$SID"; then
    # 2. Get goal info to decide agent type
    GOAL_INFO=$($E get_memory '{"key_names":["proofs/'"$TID"'/goals/'"$GID"'/definition","proofs/'"$TID"'/goals/'"$GID"'/leaf_type"]}')
    # 3. THEN spawn agent
fi
```

**Spawn the appropriate agent:**
```
Task(subagent_type="lean-collab:decomposer", prompt="STATE_DIR=$STATE_DIR. Decompose goal $GID for theorem $TID.")
Task(subagent_type="lean-collab:lean-prover", prompt="STATE_DIR=$STATE_DIR. Prove goal $GID for theorem $TID.")
```

**For multiple goals:** Claim all first, then spawn all agents in ONE message.

**⚠️ After spawning, IMMEDIATELY go back to Step 2 to check for more work.**

---

## Decision Tree (When to Decompose vs Prove)

```
┌─────────────────────────────────────────────────────────────┐
│  For each open goal from next-action.sh:                     │
│                                                              │
│  1. Does goal have leaf_type set?                            │
│     ├── YES → PROVER                                         │
│     └── NO  → continue                                       │
│                                                              │
│  2. Does goal contain ∀, ∃, →, forall, exists?               │
│     ├── YES → DECOMPOSER                                     │
│     └── NO  → continue                                       │
│                                                              │
│  3. Is it pure decidable arithmetic?                         │
│     (no variables, no transcendentals)                       │
│     ├── YES → PROVER (norm_num, native_decide)               │
│     └── NO  → DECOMPOSER                                     │
│                                                              │
│  When in doubt → DECOMPOSER                                  │
└─────────────────────────────────────────────────────────────┘
```

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
| `needs_decomposition` | Prover gave up |

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

```bash
"$SCRIPTS/compose-proof.sh" "$TID"
```

This recursively combines solutions into the final proof.
