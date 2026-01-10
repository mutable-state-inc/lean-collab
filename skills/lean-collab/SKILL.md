---
name: lean-collab
description: "Collaborative theorem proving. Checks tree state and spawns decomposer or lean-prover agent. Contains full protocol."
---

# LeanTree Collaborative Proving

Multi-agent theorem proving via Ensue Memory Network. Multiple Claude sessions coordinate to decompose, verify, and compose proofs.

---

## Ensue Namespace (Source of Truth)

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
│       └── tactic      # Tactic used to decompose
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
| `solved` | Leaf goal verified and solved |
| `needs_decomposition` | **Prover gave up - MUST spawn decomposer** |

**⚠️ CRITICAL: When you see `needs_decomposition`, ALWAYS spawn a decomposer, never a prover!**

---

## Claim Protocol

```bash
# 1. Claim
AGENT_ID="prover-$$"
TIMESTAMP=$(date +%s)
$ENSUE update_memory '{"key_name":"proofs/{TID}/goals/{GID}/status","value":"working:'$AGENT_ID':'$TIMESTAMP'"}'

# 2. Wait and verify
sleep 0.2
$ENSUE get_memory '{"key_names":["proofs/{TID}/goals/{GID}/status"]}'

# 3. Check - if another agent claimed with earlier timestamp, back off
```

---

## Leaf Detection (CRITICAL)

**"No children" ≠ "Is a leaf"**

A goal is a TRUE LEAF only if ALL conditions hold:
1. Has no children (not yet decomposed)
2. Contains NO quantifiers: `∀`, `∃`
3. Contains NO implications: `→`
4. Is decidable/computable (arithmetic, equality, simple predicates)

```
is_true_leaf(goal):
  type = goal.definition.type
  has_children = goal.children exists

  if has_children:
    return false

  # Check for complex structure that needs decomposition
  if contains(type, "∀") or contains(type, "forall"):
    return false
  if contains(type, "∃") or contains(type, "exists"):
    return false
  if contains(type, "→") or contains(type, "->"):
    return false
  if contains(type, "∧") and not is_simple_conjunction(type):
    return false

  # True leaves are decidable/computable
  return is_arithmetic(type) or is_equality(type) or is_simple_predicate(type)
```

**Examples:**
- `0 < 18` → TRUE LEAF (simple arithmetic)
- `18 * 19 > 2023` → TRUE LEAF (decidable)
- `∀ x ∈ [0,π], f(x) ≤ g(x)` → NOT A LEAF (has ∀, needs intro)
- `P ∧ Q` where P,Q are simple → TRUE LEAF
- `IsGreatest S x` → NOT A LEAF (needs constructor to split mem/ub)
- `(1/π) * x * (π-x) ≤ sin x` → **NOT A LEAF** (analytical, has Real.sin/Real.pi)
- `sin x ≤ (4/π²) * x * (π-x)` → **NOT A LEAF** (transcendental inequality)
- `Real.exp x > 0` → **NOT A LEAF** (involves Real.exp)

### Analytical Complexity Detection

**Goals with transcendentals are NOT decidable.** They require mathematical insight.

```
is_analytical(type):
  transcendentals = ["Real.sin", "Real.cos", "Real.tan",
                     "Real.exp", "Real.log", "Real.pi"]
  inequalities = ["≤", "≥", "<", ">", "\\le", "\\ge", "\\lt", "\\gt"]

  has_transcendental = any(t in type for t in transcendentals)
  is_inequality = any(op in type for op in inequalities)

  return has_transcendental and is_inequality
```

**If `is_analytical(type)` → ALWAYS use DECOMPOSER, never prover.**

---

## Core Philosophy: GRANULARITY OVER VERIFICATION

**Claude cannot solve complex problems by "thinking harder". But with the right breakdown, it can reason about a solution.**

The skill optimizes for:
1. **GRANULARITY** - Break problems into the smallest provable pieces
2. **PARALLELISM** - Many simple goals > one complex goal
3. **DISCOVERY** - Decomposition IS the intelligence; verification is mechanical

**DEFAULT = DECOMPOSE. Only verify when the path is clear.**

---

## Decision Tree

When invoked, check tree state:

```
┌─────────────────────────────────────────────────────────────┐
│              GRANULARITY-FIRST DECISION TREE                 │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Step 0: Check for "needs_decomposition" status              │
│  Any goal with status = "needs_decomposition"?               │
│  ├── YES → DECOMPOSER immediately! Prover gave up.           │
│  └── NO  → continue                                          │
│                                                              │
│  For each goal with status = "open":                         │
│                                                              │
│    Step 1: Does goal have `leaf_type`?                       │
│    $ENSUE get_memory '{"key_names":["proofs/{TID}/goals/{GID}/leaf_type"]}'│
│    ├── leaf_type = "decidable"  → PROVER (mechanical)        │
│    ├── leaf_type = "discoverable" → PROVER (search + apply)  │
│    ├── leaf_type = "algebraic"  → PROVER (ring/rewrite)      │
│    └── leaf_type NOT SET        → continue to Step 2         │
│                                                              │
│    Step 2: Count failed attempts                             │
│    $ENSUE list_keys '{"prefix":"proofs/{TID}/goals/{GID}/attempts/"}'│
│    ├── attempts >= 2 → DECOMPOSER (break it down more!)      │
│    └── attempts < 2  → continue to Step 3                    │
│                                                              │
│    Step 3: Is it PURE DECIDABLE ARITHMETIC?                  │
│    - Only integers/rationals                                 │
│    - No variables (all concrete numbers)                     │
│    - No transcendentals (sin, cos, pi, exp, log)             │
│    Examples: `0 < 18`, `18 * 19 > 2023`                      │
│    ├── YES → PROVER (native_decide/norm_num)                 │
│    └── NO  → DECOMPOSER (needs further breakdown)            │
│                                                              │
│  ⚠️ CRITICAL: When in doubt, DECOMPOSE!                      │
│  - Unknown structure → DECOMPOSE                             │
│  - Has variables → DECOMPOSE                                 │
│  - Has transcendentals → DECOMPOSE                           │
│  - Complex expression → DECOMPOSE                            │
│                                                              │
│  Are all goals "solved" or "decomposed"?                     │
│  ├── YES → Run ./scripts/compose-proof.sh to compose         │
│  └── NO  → Continue working on open goals                    │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

**KEY INSIGHT:** The skill should NEVER hope a prover "figures it out" for complex goals. If a goal doesn't have a clear `leaf_type` or isn't pure decidable arithmetic, decompose it further.

**Decomposition creates:**
- More parallelism (many agents on simple subgoals)
- Better discovery (each decomposition captures mathematical insight)
- Reusable patterns (similar subgoals can share solutions)

---

## Prover-Only Conditions (Restrictive!)

**ONLY spawn a prover when ALL of these hold:**

1. Goal has `leaf_type` set (decomposer marked it as ready), OR
2. Goal is pure decidable arithmetic (no variables, no transcendentals)

**If neither condition is met → DECOMPOSE**

This prevents token burn on complex goals that provers can't handle.

### Using lean-check.sh as Oracle

Instead of string heuristics, use `lean-check.sh` to check if decomposition is possible:

```bash
SCRIPT_DIR="$CLAUDE_PLUGIN_ROOT/scripts"
RESULT=$("$SCRIPT_DIR/lean-check.sh" "$PROJECT_DIR" "$GOAL_TYPE" "constructor" "$HYPOTHESES" 2>&1) || true

# SUBGOALS: ... → goal is decomposable, use decomposer
# VERIFIED → tactic closes goal (solved!)
# error → tactic doesn't apply, try another
```

**Lean is the oracle. No heuristics needed.**

### BAIL OUT RULE (Coordinator Decision)

**The SKILL decides when to bail out, not the agent.**

Before spawning an agent for a goal, check failed attempts:
```bash
$ENSUE list_keys '{"prefix":"proofs/{TID}/attempts/{GID}/","limit":10}'
```

- **0-2 attempts** → Try verification (if true leaf)
- **3+ attempts** → Force decomposition (verification isn't working)

This prevents token burn. The verifier just tries and records failures. The skill sees accumulated failures and switches strategy.

**Key insight:** A goal with `∀` but no children is NOT a leaf - it's a complex goal that hasn't been decomposed yet. DECOMPOSE IT.

---

## Decomposer Agent Rules

**Job:** Break complex goals into subgoals. Never verify.

### ⚠️ CRITICAL: SELF-CONTAINED GOAL TYPES

**Subgoal types MUST be standalone Lean expressions.** Expand all helpers into their mathematical form. No external definitions like `f_n`, `hf_deriv2`, etc.

**What to decompose:**
- Root goal (ALWAYS)
- Goals containing ∀, ∃, →
- Goals with multiple conjuncts (∧)
- Goals requiring structural reasoning

**What is a leaf (don't decompose):**
- Pure arithmetic: `2109 > 2023`
- Simple decidable: `0 < 18`
- Trivial equality: `rfl`

**IsLeast decomposition:**
```
IsLeast {n : ℕ | 0 < n ∧ n * (n+1) * (2*n+1) / 6 > 2023} 18
├── membership: 0 < 18 ∧ 18 * 19 * 37 / 6 > 2023  ← EXPANDED
└── minimality: ∀ m : ℕ, (0 < m ∧ m * (m+1) * (2*m+1) / 6 > 2023) → 18 ≤ m
Tactic: constructor
```

**After decomposing:**
```bash
# Create subgoals (types must be SELF-CONTAINED!)
$ENSUE create_memory '{"items":[
  {"key_name":"proofs/{TID}/goals/{SUB}/definition","value":"{\"type\":\"STANDALONE_LEAN_TYPE\"}","description":"subgoal","embed":true},
  {"key_name":"proofs/{TID}/goals/{SUB}/status","value":"open","description":"status","embed":false},
  {"key_name":"proofs/{TID}/goals/{SUB}/parent","value":"{GID}","description":"parent","embed":false}
]}'

# Mark parent decomposed with tactic
$ENSUE update_memory '{"key_name":"proofs/{TID}/goals/{GID}/status","value":"decomposed"}'
$ENSUE update_memory '{"key_name":"proofs/{TID}/goals/{GID}/tactic","value":"constructor"}'
$ENSUE update_memory '{"key_name":"proofs/{TID}/goals/{GID}/children","value":"[\"sub1\",\"sub2\"]"}'
```

**❌ BAD:** `|f_18''(0)| > 2023` (undefined `f_18`)
**✓ GOOD:** `18 * 19 * 37 / 6 > 2023` (pure arithmetic)

---

## Lean-Prover Agent Rules

**Job:** Verify leaf goals with Lean, compose final proof.

### ⚠️ CRITICAL: SELF-CONTAINED VERIFICATION

**Every verification MUST be standalone.** The goal type comes from Ensue's `goals/{id}/definition`, NOT from any local .lean file. Tactics cannot reference external definitions.

**Step 1: Get goal type from Ensue**
```bash
$ENSUE get_memory '{"key_names":["proofs/{TID}/goals/{GID}/definition"]}'
# Use the "type" field as GOAL_TYPE
```

**Step 2: Verify with standalone file**
```bash
VERIFY_DIR=$(mktemp -d)
cat > "$VERIFY_DIR/check.lean" << 'EOF'
import Mathlib.Tactic

-- GOAL_TYPE from Ensue definition, TACTIC uses only Mathlib
theorem check : {GOAL_TYPE} := by
  {TACTIC}
EOF
cd /private/tmp/putnam-test && lake env lean "$VERIFY_DIR/check.lean" 2>&1
rm -rf "$VERIFY_DIR"
```

**Allowed tactics (Mathlib only):**
- `native_decide`, `norm_num`, `decide`, `rfl`
- `simp` (no custom lemmas), `omega`, `ring`
- `constructor`, `intro`, `by_contra`, `push_neg`
- `interval_cases` (for bounded case splits)

**❌ FORBIDDEN:**
- `hf_deriv2`, `f_n`, or ANY external definition
- `rw [lemma]` where lemma is not from Mathlib
- Any identifier not in Mathlib.Tactic

### Tactic Attempt Limit

**Try up to 3 tactics. Record failures. Release goal.**

The SKILL (see Decision Tree above) monitors attempts and forces decomposition after 3 failures.

**On success:**
```bash
$ENSUE create_memory '{"items":[{"key_name":"proofs/{TID}/solutions/{GID}","value":"{TACTIC}","description":"solution","embed":true}]}'
$ENSUE update_memory '{"key_name":"proofs/{TID}/goals/{GID}/status","value":"solved"}'
```

**On failure:**
```bash
HASH=$(echo -n "{TACTIC}" | shasum | cut -c1-8)
$ENSUE create_memory '{"items":[{"key_name":"proofs/{TID}/attempts/{GID}/'$HASH'","value":"{\"tactic\":\"{TACTIC}\",\"error\":\"{ERR}\"}","description":"failed","embed":false}]}'
```

---

## Composition

When all goals are solved/decomposed, compose final proof.

### Automatic Composition Script

```bash
# Run from plugin root after all goals are solved
./scripts/compose-proof.sh {theorem-id}
```

This script:
1. Fetches all goals from Ensue
2. Caches solutions locally
3. Recursively composes bottom-up (skips abandoned/invalid branches)
4. Stores composed solutions back to `proofs/{TID}/solutions/{goal-id}`
5. Produces root proof at `proofs/{TID}/solutions/root`

### Manual Composition Algorithm

```
compose(goal_id):
  status = goals/{goal_id}/status

  if status == "solved":
    return solutions/{goal_id}

  if status == "decomposed":
    tactic = goals/{goal_id}/tactic
    children = goals/{goal_id}/children
    child_proofs = [compose(c) for c in children]

    return tactic + "\n" + "· " + child_proofs[0] + "\n· " + child_proofs[1] + ...
```

**Example:**
```lean
theorem putnam_2023_a1 : IsLeast {n | 0 < n ∧ |f_n''(0)| > 2023} 18 := by
  constructor
  · norm_num
  · intro m hm; omega
```

Store: `proofs/{TID}/final-proof`

---

## Repair Protocol (When Composed Proof Has Errors)

**⚠️ CRITICAL: Do NOT fix syntax in the composed file. Fix the SOURCE solution in Ensue.**

When `compose-proof.sh` produces a proof with Lean errors:

### Step 1: Parse error to identify the broken goal

```bash
# Run Lean and capture errors
cd /private/tmp/putnam-test && lake env lean /tmp/composed.lean 2>&1 | head -20

# Error format: "/tmp/composed.lean:42:5: error: unknown identifier 'foo'"
# The line number maps to a specific goal's solution
```

### Step 2: Trace line to goal

The composed proof structure is:
```
root tactic
· child1 solution  ← line 2-10
· child2 solution  ← line 11-20
  · grandchild...
```

Match the error line to the goal ID by checking `proofs/{TID}/solutions/{goal-id}`.

### Step 3: Fix the source solution

```bash
# Get the broken goal's current solution
$ENSUE get_memory '{"key_names":["proofs/{TID}/solutions/{BROKEN_GOAL}"]}'

# Write a VERIFIED fix
cat > /tmp/fix.lean << 'EOF'
import Mathlib
theorem check : {GOAL_TYPE} := by
  {FIXED_TACTIC}
EOF
cd /private/tmp/putnam-test && lake env lean /tmp/fix.lean 2>&1

# If it compiles, store the fix
$ENSUE update_memory '{"key_name":"proofs/{TID}/solutions/{BROKEN_GOAL}","value":"{FIXED_TACTIC}"}'
```

### Step 4: Re-compose

```bash
./scripts/compose-proof.sh {TID}
# Verify the new composition compiles
```

### Common Syntax Issues in Solutions

| Error | Cause | Fix |
|-------|-------|-----|
| `unexpected token '·'` | Bullet without `by` | Wrap in `by` block |
| `unknown identifier` | Reference to undefined helper | Inline the helper or use Mathlib lemma |
| `expected ':='` | Comment without `--` | Add `--` prefix |
| `type mismatch` | Wrong lemma application | Check lemma signature with `#check` |

**❌ NEVER:**
- Edit the composed .lean file directly (it will be overwritten)
- Write Python/sed scripts to fix indentation
- Guess at syntax fixes without Lean verification

**✓ ALWAYS:**
- Trace errors to source goal in Ensue
- Verify fix compiles before storing
- Re-run compose-proof.sh after fixing

---

## Collective Intelligence

**Before trying a tactic, check if it already failed:**
```bash
$ENSUE list_keys '{"prefix":"proofs/{TID}/attempts/{GID}/","limit":50}'
```

**Search for similar solved goals:**
```bash
$ENSUE search_memories '{"query":"{goal_type}","prefix":"proofs/","limit":5}'
```

**Search tactics library for relevant lemmas:**
```bash
$ENSUE search_memories '{"query":"{goal_type}","prefix":"tactics/library/","limit":5}'
```

The tactics library is populated automatically on session start with common Mathlib lemmas. Agents should ALWAYS query collective intelligence before trying tactics.

---

## Forbidden Actions (Token Efficiency)

- ❌ **Guess lemma names** - Query collective intelligence or use `exact?`
- ❌ **grep/find/Glob on files** - ALL KNOWLEDGE IS IN ENSUE
- ❌ **More than 3 tactic attempts per goal** - Record and release
- ❌ **Use Search, Glob, or Grep tools** - Query `$ENSUE search_memories` instead
- ❌ **Search Mathlib or .lake directories** - USE COLLECTIVE INTELLIGENCE
- ❌ Read external .lean files
- ❌ Use WebSearch or WebFetch
- ❌ Exit before proof is complete

**The collective intelligence (Ensue) is the knowledge base. Query it, don't search files.**

---

## Invocation

**Step 1: Read config and check state**
```bash
THEOREM_ID=$(cat .lean-collab.json | jq -r '.theorem_id')
ENSUE="$(find ~/.claude/plugins/cache -name 'ensue-api.sh' -path '*/ensue-memory/*' 2>/dev/null | head -1)"
$ENSUE list_keys "{\"prefix\":\"proofs/$THEOREM_ID/goals/\",\"limit\":50}"
```

**Step 2: Spawn agents using plugin definitions**

⚠️ **CRITICAL: Use the plugin's agent types, not custom prompts!**

The `subagent_type` MUST match the agent name from the plugin (`lean-prover` or `decomposer`).
The agent will receive its full protocol from `agents/lean-prover.md` or `agents/decomposer.md`.

```
Task(subagent_type="lean-prover", prompt="Work on theorem: $THEOREM_ID", run_in_background=true)
Task(subagent_type="decomposer", prompt="Work on theorem: $THEOREM_ID", run_in_background=true)
```

**DO NOT write custom prompts that bypass the agent protocols!**

The agent definitions contain:
- Token-efficient tactic search (exact? first)
- 3-attempt limit with Ensue recording
- Proper decomposition vs verification logic

**Step 3: Monitor progress**
```bash
$ENSUE list_keys "{\"prefix\":\"proofs/$THEOREM_ID/goals/\",\"limit\":50}"
# Check for status changes: open → working → solved/decomposed
```

Multiple sessions = spawn more background agents = more parallel power.

**Step 4: Compose final proof**

When all goals are `solved` or `decomposed`:
```bash
cd "$CLAUDE_PLUGIN_ROOT" && ./scripts/compose-proof.sh "$THEOREM_ID"
```

This recursively combines all solutions into the final proof at `proofs/{TID}/solutions/root`.
