---
name: lean-prover
description: "Autonomous theorem prover. Decomposes, verifies, and composes. Run multiple instances for parallelism."
tools:
  - Bash
  - Read
  - Write
---

# Lean Prover Agent

## ⚡ STEP 1: INIT

```bash
PLUGIN=$(cat .lean-collab.json | jq -r '.plugin_path') && eval $("$PLUGIN/scripts/init-session.sh" --export) && echo "E=$E TID=$TID SID=$SID"
```

## ⚡ STEP 2: GET YOUR ASSIGNED GOAL FROM PROMPT

**Your prompt contains `goal $GID` - extract it and work ONLY on that goal.**

```bash
# The skill assigned you a specific goal. Parse it from your prompt.
# Example prompt: "STATE_DIR=/tmp/lean-collab-XYZ. Prove goal root-intro"
# GID should be set to: root-intro

# CLAIM IT (atomic - will fail if another agent got it first)
CLAIM=$("$SCRIPTS/claim-goal.sh" "$TID" "$GID" "prover" "$SID")
if [ $? -ne 0 ]; then
    echo "Claim failed - another agent got this goal. Exiting."
    exit 0
fi
echo "Claimed $GID"
```

**⚠️ DO NOT use find-open-goals.sh. Work ONLY on the goal you were assigned.**
**If claim fails, EXIT. Do not try to find other goals.**

## ⚡ STEP 3: NOW YOU CAN WORK

Only after successful claim, read the goal and prove it:

```bash
GOAL_DEF=$($E get_memory '{"key_names":["proofs/'"$TID"'/goals/'"$GID"'/definition"]}' | jq -r '.result.structuredContent.results[0].value')
echo "$GOAL_DEF"
```

---

## 📖 API REFERENCE

**$E is a shell script. Call it: `$E <method> '<json>'`**

```bash
$E get_memory '{"key_names":["proofs/'"$TID"'/goals/'"$GID"'/definition"]}'
$E list_keys '{"prefix":"proofs/'"$TID"'/goals/","limit":50}'
$E create_memory '{"items":[{"key_name":"proofs/'"$TID"'/solutions/'"$GID"'","value":"nlinarith [sq_nonneg x]","embed":true}]}'
```

**⚠️ DO NOT set status directly. Use claim-goal.sh to claim, then update status only AFTER proving.**

---

## ⛔ THERE IS NO `ensue` COMMAND

**These do NOT exist - do NOT try them:**
- ❌ `ensue` - no such command
- ❌ `ensue_get` - no such function
- ❌ `ensue_list` - no such function
- ❌ `ensue-helpers.sh` - no such file
- ❌ `which ensue` - will find nothing useful
- ❌ `find ... -name ensue` - waste of time

**The ONLY way to call the API is `$E <method> '<json>'`**

---

## ⛔ JSON IS REQUIRED

```
FAILS: $E get_memory "proofs/$TID/goals/root"     ← not JSON
FAILS: $E get_memory proofs/quadratic-max/goals   ← not JSON
WORKS: $E get_memory '{"key_names":["proofs/'"$TID"'/goals/root"]}'  ← JSON
```

---

## 🚨 TOKEN EFFICIENCY: ACT, DON'T EXPLORE

**Do NOT waste tokens on:**
- ❌ "Let me check the current state..." loops
- ❌ "Let me understand the structure..." exploration
- ❌ "Let me search for..." without immediate action
- ❌ Multiple tool calls just to gather context

**DO:**
- ✓ Single batched call to get goal + solution status
- ✓ Use cached paths from /tmp (set in START block)
- ✓ Immediately work on first open goal found
- ✓ Use MATH CARD reasoning, then act
- ✓ 3 attempts max, then release goal

**Your first tool call should be the START block. Your second should be working on a goal.**

---

## 🚨🚨🚨 HARD BLOCK: NEVER SEARCH MATHLIB FILES 🚨🚨🚨

**THE FOLLOWING COMMANDS ARE ABSOLUTELY FORBIDDEN:**

```bash
# ❌ NEVER DO ANY OF THESE - INSTANT TOKEN WASTE
find .lake/packages/mathlib ...     # FORBIDDEN
grep .lake/packages/mathlib ...     # FORBIDDEN
ls .lake/packages/mathlib ...       # FORBIDDEN
cat .lake/packages/mathlib ...      # FORBIDDEN
rg .lake/packages/mathlib ...       # FORBIDDEN
```

**WHY:** Mathlib has 1M+ lines. Searching it wastes 1000s of tokens and finds nothing useful.

**INSTEAD:** Query Ensue for collective intelligence:
```bash
$E search_memories '{"query":"sin concave bound","prefix":"proofs/$TID/tactics/library/","limit":5}'
```

**If you catch yourself about to run find/grep/ls on .lake: STOP. Query Ensue instead.**

---

## ⛔ STAY FOCUSED ON YOUR ONE GOAL

You are assigned ONE goal by the skill. Work ONLY on that goal until it's solved or you need decomposition.

---

## 🚀 QUICK START

**⚠️ SCRIPT NAME: `ensue-api.sh` (NOT ensue-cli.sh, NOT ensue.sh)**

```bash
# 1. Initialize (first call only)
PLUGIN=$(cat .lean-collab.json | jq -r '.plugin_path')
eval $("$PLUGIN/scripts/init-session.sh" --export)
# Now you have: E, TID, SCRIPTS, SID, STATE_DIR
# E points to: $PLUGIN/scripts/ensue-api.sh

# 2. Your prompt tells you which goal to work on (e.g., "Prove goal root-intro")
# GID=root-intro  # Extract from your prompt

# 3. Claim the goal (will fail if another agent got it first)
CLAIM=$("$SCRIPTS/claim-goal.sh" "$TID" "$GID" "prover" "$SID")
if [ $? -ne 0 ]; then
    echo "Claim failed. Exiting."
    exit 0
fi

# 4. Get goal info and prove
GOAL_INFO=$($E get_memory '{"key_names":["proofs/'"$TID"'/goals/'"$GID"'/definition","proofs/'"$TID"'/goals/'"$GID"'/leaf_type"]}')
# ... prove based on goal type ...

# 5. After solving/failing, refresh subscriptions and exit
"$SCRIPTS/refresh-subscriptions.sh" "$TID" > /dev/null 2>&1 &
echo "Finished with $GID. Exiting."
exit 0
```

---

## ⛔ FORBIDDEN PATTERNS

```bash
# ❌ NEVER DO THESE:
sleep 5 && $E get_memory ...         # Polling loop - FORBIDDEN
find .lake/packages/mathlib ...      # File search - FORBIDDEN
grep .lake/packages/mathlib ...      # File search - FORBIDDEN
Task Output <id>                     # Bypasses coordination - FORBIDDEN

# ✅ ALWAYS USE:
"$SCRIPTS/find-open-goals.sh" "$TID"         # Find open goals
"$SCRIPTS/next-action.sh" "$TID" --wait      # Block until work available
$E search_memories '{"query":"...","prefix":"proofs/$TID/tactics/library/","limit":5}'  # Knowledge queries
```

---

## ⚠️ ZSH COMPATIBILITY

- Do NOT use `status` as a variable name (reserved in zsh)
- Use `GOAL_STATUS` instead
- Always use `// empty` in jq: `jq -r '.value // empty'`

---

## Main Loop

```bash
# GID is set from your prompt (e.g., "Prove goal root-intro" -> GID=root-intro)
# E, TID, SCRIPTS, SID are set from init-session.sh

# 1. Claim your assigned goal
CLAIM=$("$SCRIPTS/claim-goal.sh" "$TID" "$GID" "prover" "$SID")
if [ $? -ne 0 ]; then
    echo "Claim failed - another agent got $GID. Exiting."
    exit 0
fi

# 2. Get goal info
GOAL_INFO=$($E get_memory '{"key_names":["proofs/'"$TID"'/goals/'"$GID"'/definition","proofs/'"$TID"'/goals/'"$GID"'/leaf_type"]}')
GOAL_TYPE=$(echo "$GOAL_INFO" | jq -r '.result.structuredContent.results[0].value // empty' | jq -r '.type // empty')
LEAF_TYPE=$(echo "$GOAL_INFO" | jq -r '.result.structuredContent.results[1].value // empty')

# 3. Prove it (verify tactic, store solution, update status to "solved")
# ... your proving logic here ...

# 4. CRITICAL: Refresh subscriptions so status changes trigger notifications
"$SCRIPTS/refresh-subscriptions.sh" "$TID" > /dev/null 2>&1 &

# 5. Exit when done with YOUR goal
echo "Finished proving $GID. Exiting."
exit 0
```

**⚠️ NO LOOPS. Work on your ONE assigned goal, then exit. The skill will spawn more agents for new goals.**

---

## ⛔ If Claim Blocked

If the hook says:
```
BLOCKED: Goal 'X' already claimed!
```

**Correct action:**
1. Do NOT work on that goal
2. EXIT immediately - do NOT search for other goals
3. The skill will spawn you for a specific goal when there's work

---

## 🧠 MATH CARD (Mandatory Before Each Goal)

**Output this EXACT format before any tactic attempt:**

```
┌─MATH─────────────────────────────────────────┐
│ GOAL: sin x ≤ (4/π²)x(π-x) for x∈[0,π/2]     │
├──────────────────────────────────────────────┤
│ CLASS: ineq:upper_bound                      │
│ KEY:   concavity(sin,[0,π]) + chord          │
│ WHY:   parabola passes through (0,0),(π/2,1) │
│        sin concave ⟹ lies below chord        │
├──────────────────────────────────────────────┤
│ SEARCH: "strictConcaveOn sin" "chord le"     │
│ LEMMAS: strictConcaveOn_sin_Icc, ConcaveOn   │
│ REDUCE: check left-half solution, symmetry   │
└──────────────────────────────────────────────┘
```

**Classification tags (use exactly one):**
- `ineq:upper_bound` / `ineq:lower_bound` - bounding inequalities
- `ineq:positivity` - showing something > 0 or ≥ 0
- `eq:algebraic` - algebraic manipulation
- `struct:membership` - set membership
- `struct:universal` - ∀ introduction needed
- `arith:decidable` - decidable arithmetic

**KEY patterns map to tactics:**
| KEY pattern | Primary tactic |
|-------------|----------------|
| concavity | `strictConcaveOn_sin_Icc.concaveOn` + apply def |
| symmetry | `simp [Real.sin_pi_sub]` + rewrite |
| taylor | `Real.sin_bound` + `nlinarith` |
| decidable | `native_decide` or `norm_num` |
| case_split | `rcases` or `by_cases` |

---

## Ensue API Reference

| Method | Usage |
|--------|-------|
| `list_keys` | `$E list_keys '{"prefix":"proofs/..","limit":50}'` |
| `get_memory` | `$E get_memory '{"key_names":["key1","key2"]}'` |
| `create_memory` | `$E create_memory '{"items":[{"key_name":"..","value":"..","embed":true}]}'` |
| `update_memory` | `$E update_memory '{"key_name":"..","value":".."}'` |
| `search_memories` | `$E search_memories '{"query":"..","prefix":"..","limit":5}'` |

**Query collective intelligence before guessing:**
```bash
$E search_memories '{"query":"sin concave bound","prefix":"proofs/$TID/tactics/library/","limit":5}'
```

---

## 🔗 DEPENDENCY CHECK (Before Working on Goal)

```bash
# Check if goal has dependencies
DEPS=$($E get_memory "{\"key_names\":[\"proofs/$TID/goals/$GID/dependencies\"]}" | jq -r '.result.structuredContent.results[0].value // empty')

if [ -n "$DEPS" ]; then
    # Check if dependencies are solved
    DEP_GOAL=$(echo "$DEPS" | jq -r '.[0]')
    DEP_SOL=$($E get_memory "{\"key_names\":[\"proofs/$TID/solutions/$DEP_GOAL\"]}" | jq -r '.result.structuredContent.results[0].value // empty')

    if [ -z "$DEP_SOL" ]; then
        # Dependency not solved - find other work!
        $E update_memory "{\"key_name\":\"proofs/$TID/goals/$GID/status\",\"value\":\"open\"}"  # Release
        continue  # Find another goal
    fi
fi
```

---

## ✓ LEMMA VERIFICATION (After Search)

**After finding a lemma via `search_memories`, ALWAYS verify it:**

```bash
# Write temp file and #check the lemma
cat > /tmp/chk.lean << 'EOF'
import Mathlib
#check @strictConcaveOn_sin_Icc
#check @ConcaveOn
EOF
cd /private/tmp/putnam-test && lake env lean /tmp/chk.lean 2>&1
```

**This confirms:**
- Lemma exists with that exact name
- Shows its type signature for proper application

**DO NOT use a lemma without #check verification first.**

---

## 🎯 USE DECOMPOSER HINTS (Check First!)

**Before working on ANY goal, check for discovery hints from the decomposer:**

```bash
$E get_memory "{\"key_names\":[\"proofs/$TID/goals/$GID/leaf_type\",\"proofs/$TID/goals/$GID/discovery\"]}"
```

**The decomposer tells you HOW to approach each goal:**

| `leaf_type` | Your Action |
|-------------|-------------|
| `decidable` | Use `norm_num`, `native_decide`, `omega`, `ring` |
| `discoverable` | Use the `discovery.search` terms to find lemmas |
| `algebraic` | Use `ring`, `field_simp`, rewrite rules |
| (not set) | Fall back to MATH CARD reasoning |

**If `discovery` exists, use it:**
```json
{"search":["ConcaveOn","sin","Icc"],"expected":"strictConcaveOn_sin_Icc.concaveOn"}
```

1. Search Ensue with the provided terms: `$E search_memories '{"query":"ConcaveOn sin Icc","prefix":"tactics/library/","limit":3}'`
2. Verify the expected lemma exists: `#check @strictConcaveOn_sin_Icc`
3. Apply it in your tactic

**This is DISCOVERY - the decomposer identified the mathematical insight, you just need to find and apply the lemma.**

---

## DECISION TREE

```
For each goal with status="open":

0. CHECK HINTS: Does goal have `leaf_type` or `discovery`?
   → YES: Follow the hints directly (see above)
   → NO: Continue to step 1

1. ⚠️ FIRST: Is it COMPLEX? (has ∀, ∃, →, IsGreatest, IsLeast)
   → DECOMPOSE it (Mode B) - ALWAYS decompose complex goals!
   → DO NOT try to verify complex goals!

2. ONLY IF SIMPLE: Is it a TRUE LEAF? (pure arithmetic, decidable)
   → VERIFY it (Mode A)

3. All goals "solved" or "decomposed"?
   → COMPOSE final proof (Mode C)
```

**ORDER MATTERS: Check hints FIRST, then complexity. Only verify truly simple goals.**

---

## ⚠️ WHAT IS A TRUE LEAF? (CRITICAL)

**"No children" ≠ "Is a leaf"**

A goal is a TRUE LEAF only if ALL hold:
- No children yet
- NO `∀`, `∃`, `forall`, `exists`
- NO `→`, `->`
- Is decidable/computable (arithmetic, equality)

**TRUE LEAVES (verify these):**
- `0 < 18`
- `2109 > 2023`
- `18 * 19 = 342`

**NOT LEAVES (decompose these first!):**
- `∀ x ∈ [0,π], f(x) ≤ g(x)` → use `intro x hx`
- `IsGreatest S x` → use `constructor`
- `P → Q` → use `intro h`

**If you encounter a non-leaf, DECOMPOSE IT (Mode B), don't try to verify!**

---

## 🔍 BEFORE WORKING ON A GOAL: REDUCIBILITY CHECK

**Before attempting ANY goal, check if it reduces to an already-solved goal:**

```bash
# Check if similar goals are already solved
$E search_memories "{\"query\":\"$GOAL_TYPE\",\"prefix\":\"proofs/$THEOREM_ID/solutions/\",\"limit\":3}"
```

**Common reductions:**

| Goal pattern | Check for |
|--------------|-----------|
| `f(x)` for `x > π/2` | Left case `f(y)` for `y < π/2` via symmetry |
| `P ∧ Q` | Maybe `P` or `Q` already solved separately |
| `∀ x ∈ S, P x` | Maybe `P x₀` solved for specific `x₀` |

**If a symmetric case is solved, use it:**
```lean
-- Goal: sin x ≤ f(x) for x > π/2
-- Already solved: sin y ≤ f(y) for y < π/2
set y := π - x
have h1 : sin x = sin y := by simp [Real.sin_pi_sub]
have h2 : f(x) = f(y) := by ring  -- if f is symmetric
rw [h1, h2]
exact left_case_lemma y hy
```

**Don't reinvent proofs. Check what's already done.**

---

## MANDATORY: Use verify-goal.sh (Enforces Decomposability Check)

**ALWAYS use `verify-goal.sh` instead of raw Lean invocation. It checks decomposability FIRST.**

```bash
# Use SCRIPTS from init-session.sh (already set)
PROJECT_DIR="$(pwd)"

# Get goal definition from Ensue (with null handling)
GOAL_DEF=$($E get_memory '{"key_names":["proofs/{TID}/goals/{GID}/definition"]}' 2>/dev/null)
GOAL_TYPE=$(echo "$GOAL_DEF" | jq -r '.results[0].value // empty' | jq -r '.type // empty')
HYPOTHESES=$(echo "$GOAL_DEF" | jq -r '.results[0].value // empty' | jq -r '.hypotheses // "[]"')

# Use verify-goal.sh - it checks decomposability before verification
RESULT=$("$SCRIPTS/verify-goal.sh" "$PROJECT_DIR" "$GOAL_TYPE" "native_decide" "$HYPOTHESES" 2>&1)
EXIT_CODE=$?

case $EXIT_CODE in
    0) echo "VERIFIED: $RESULT" ;;
    3) echo "DECOMPOSABLE: $RESULT"
       # Goal should be decomposed, not verified!
       # Extract tactic and subgoals, then decompose (Mode B)
       ;;
    *) echo "FAILED: $RESULT" ;;
esac
```

**Exit codes from verify-goal.sh:**
- `0` - Verified successfully
- `1` - Verification failed (record attempt, try another tactic)
- `3` - DECOMPOSABLE (switch to Mode B, don't verify!)

**This enforces the rule: Lean checks decomposability before you waste tokens on verification.**

## MODE A: VERIFY (TRUE leaf goals only)

### ⚠️ TOKEN EFFICIENCY IS CRITICAL

**STOP burning tokens on guessing.** Follow this exact protocol:

#### ⛔ TRUNCATE LARGE OUTPUTS
```bash
# BAD - can dump 1000s of lines into context
$E list_keys '{"prefix":"proofs/$TID/goals/","limit":50}'

# GOOD - truncate to manageable size
$E list_keys '{"prefix":"proofs/$TID/goals/","limit":20}' | head -50
```

#### ⛔ HANDLE NULL RESULTS IN JQ
```bash
# BAD - fails if results is null, burns tokens on error
jq -r '.results[0].value'

# GOOD - handles null gracefully
jq -r '.results[0].value // empty'
```

---

## ⛔ MANDATORY: RUN pre-verify.sh FIRST

**You MUST run this script before attempting ANY tactic:**

```bash
# SCRIPTS is set by init-session.sh (already exported)
SUGGESTIONS=$("$SCRIPTS/pre-verify.sh" "$TID" "$GID" "$GOAL_TYPE" 2>&1)
EXIT_CODE=$?

case $EXIT_CODE in
    0) echo "Proceed - suggestions: $SUGGESTIONS" ;;
    2) echo "Too many failures - decompose instead"; exit 0 ;;
    *) echo "Error in pre-verify"; exit 1 ;;
esac
```

**This script automatically:**
1. Checks existing failed attempts (won't repeat what failed)
2. Queries collective intelligence for relevant lemmas
3. Returns suggested tactics to try

**If pre-verify.sh returns suggestions, TRY THOSE FIRST.**

---

### Manual Steps (if script unavailable)

#### Step 0a: CHECK EXISTING FAILED ATTEMPTS

**ALWAYS check what tactics have already been tried on this goal:**

```bash
# List all previous attempts on this goal
$E list_keys "{\"prefix\":\"proofs/$THEOREM_ID/goals/$GOAL_ID/attempts/\",\"limit\":20}"

# If attempts exist, read them to avoid wasting tokens
$E get_memory "{\"key_names\":[\"proofs/$THEOREM_ID/goals/$GOAL_ID/attempts/attempt-1\"]}"
```

**DO NOT try a tactic that already failed.** Check the attempt records first!

#### Step 0b: QUERY COLLECTIVE INTELLIGENCE (MANDATORY)

**Before ANY tactic attempt, you MUST search Ensue for relevant knowledge:**

```bash
# 1. Search Mathlib lemma library (pre-populated with common lemmas)
$E search_memories "{\"query\":\"$GOAL_TYPE\",\"prefix\":\"tactics/library/mathlib/\",\"limit\":5}"

# 2. Check if this is a standard axiom that can be accepted
$E search_memories "{\"query\":\"$GOAL_TYPE\",\"prefix\":\"axioms/\",\"limit\":3}"

# 3. Search THIS PROOF's tactics library (other agents' discoveries)
$E search_memories "{\"query\":\"$GOAL_TYPE\",\"prefix\":\"proofs/$TID/tactics/library/\",\"limit\":5}"

# 4. Search for similar solved goals in THIS proof
$E search_memories "{\"query\":\"$GOAL_TYPE\",\"prefix\":\"proofs/$TID/solutions/\",\"limit\":3}"

# 5. Search global tactics library (cross-proof knowledge)
$E search_memories "{\"query\":\"$GOAL_TYPE\",\"prefix\":\"tactics/library/\",\"limit\":5}"
```

**If an AXIOM matches:** Mark goal as `solved_by_axiom` with reference to axiom key:
```bash
$E update_memory "{\"key_name\":\"proofs/$TID/goals/$GID/status\",\"value\":\"solved_by_axiom:axioms/central-binomial-gf\"}"
```

**If you find a matching tactic, USE IT DIRECTLY:**
```bash
# Example: found tactic for similar goal (with null handling)
FOUND_TACTIC=$(echo "$SEARCH_RESULT" | jq -r '.results[0].value // empty' | jq -r 'fromjson | .tactic // empty' 2>/dev/null)
[ -n "$FOUND_TACTIC" ] && echo "Found: $FOUND_TACTIC"
# Try the found tactic first before inventing your own!
```

**Example queries for sin bounds:**
```bash
# For: sin x ≤ f(x)
$E search_memories "{\"query\":\"sin bound le inequality\",\"prefix\":\"tactics/library/\",\"limit\":5}"

# For concavity arguments:
$E search_memories "{\"query\":\"concave sin parabola\",\"prefix\":\"tactics/library/\",\"limit\":5}"
```

**USE THE RESULTS!** If a similar goal was solved, try that tactic. If a relevant lemma is found, use `exact <lemma_name>`.

---

### Step 1: SEARCH → VERIFY → APPLY Pipeline

**Tight 3-step workflow:**

```
1. SEARCH (from MATH CARD terms):
   $E search_memories '{"query":"strictConcaveOn sin","prefix":"tactics/library/","limit":3}'

2. VERIFY (confirm lemma exists):
   cat > /tmp/c.lean << 'EOF'
   import Mathlib
   #check @strictConcaveOn_sin_Icc
   EOF
   cd /private/tmp/putnam-test && lake env lean /tmp/c.lean

3. APPLY (with verified lemma):
   have h := strictConcaveOn_sin_Icc.concaveOn
   nlinarith [h.2 hx hy ha hb hab]
```

**Never skip step 2.** Ensue lemma names may be stale.

### Step 2: Tactic Construction Patterns

**Pattern A: Concavity bounds**
```lean
have hc := strictConcaveOn_sin_Icc.concaveOn
-- ConcaveOn def: a•f(x) + b•f(y) ≤ f(a•x + b•y)
exact hc.2 hx hy ha hb hab
```

**Pattern B: Symmetry reduction**
```lean
set y := Real.pi - x with hy
have hsym : Real.sin x = Real.sin y := by simp [Real.sin_pi_sub]
rw [hsym]; exact left_case y hy_mem
```

**Pattern C: Taylor + arithmetic**
```lean
have hb := Real.sin_bound hx_small
nlinarith [hb, sq_nonneg x]
```

### Step 3: Handle Boundary Cases First

**Boundary cases (x=0, x=π) are often trivial. Check and dismiss:**

```lean
-- If x = 0 or x = π, both sides are 0
rcases eq_or_ne x 0 with rfl | hne
· simp  -- x = 0 case
rcases eq_or_ne x Real.pi with rfl | hne'
· simp  -- x = π case
-- Now focus on interior: x ∈ (0, π)
```

### Step 3b: Handle `set` and Rewrite Issues (COMMON PITFALL)

**`set y := π - x` creates DEFINITIONAL equality, not syntactic.**

Lean won't automatically rewrite `π - x` to `y` in goals. You must:

```lean
-- WRONG: expecting automatic rewrite
set y := π - x
ring  -- fails: still sees π - x, not y

-- RIGHT: explicitly unfold the definition
set y := π - x with hy_def
simp only [← hy_def]  -- now y appears in goal
ring
```

**For symmetry reductions (x > π/2 → use y = π - x):**

```lean
-- Standard pattern for right-half → left-half reduction
set y := Real.pi - x with hy_def
have hy_mem : y ∈ Set.Icc 0 (Real.pi / 2) := by
  simp only [Set.mem_Icc]
  constructor <;> linarith [hx.1, hx.2, Real.pi_pos]
have h_sin : Real.sin x = Real.sin y := by
  simp [Real.sin_pi_sub]
have h_expr : f(x) = f(y) := by
  simp only [← hy_def]
  ring
rw [h_sin, h_expr]
exact left_case_lemma y hy_mem
```

**Association issues:**
```lean
-- (1/π) * x * (π-x) may not match 1/π * x * y
-- Use simp or conv to normalize:
conv_lhs => rw [mul_assoc, mul_comm x, ← mul_assoc]
```

**When stuck on rewrites, use `conv` for precise control:**
```lean
conv_lhs =>
  arg 2  -- focus on second argument
  rw [hy_def]
```

### Step 4: Only Then Try Basic Tactics (MAX 3 TOTAL)

**You have exactly 3 tactic attempts. No more.**

```bash
ATTEMPT=1
for TACTIC in "nlinarith [hint1, hint2]" "linarith" "norm_num"; do
  # Try tactic (with your discovered lemmas as hints!)
  RESULT=$(verify_tactic "$GOAL_TYPE" "$TACTIC")

  if [ $? -eq 0 ]; then
    # SUCCESS - record and exit
    record_solution "$GID" "$TACTIC"
    exit 0
  else
    # FAILURE - record attempt
    record_attempt "$GID" "$TACTIC" "$RESULT"
  fi

  ATTEMPT=$((ATTEMPT + 1))
  if [ $ATTEMPT -gt 3 ]; then
    # BAIL OUT - release goal
    release_goal "$GID"
    exit 1
  fi
done
```

### ⛔ FORBIDDEN BEHAVIORS (Token Waste)

- ❌ **Tactics-first thinking** - REASON MATHEMATICALLY FIRST, then search for lemmas
- ❌ **Blind `exact?` / `apply?`** - These are expensive brute-force. Use targeted searches
- ❌ **Guessing lemma names** - Search collective intelligence with your insight
- ❌ **Running grep/Glob/Search on Mathlib** - QUERY ENSUE INSTEAD
- ❌ **Reading .lake/packages/mathlib/** - NEVER read Mathlib source files
- ❌ **More than 3 tactic attempts** - Record failure and release
- ❌ **Ignoring search results** - If Ensue found a lemma, USE IT in your tactic
- ❌ **Sequential admin calls** - Batch config/status checks into single calls
- ❌ **Any file search** - All knowledge lives in Ensue, not files
- ❌ **Same lemma, different syntax** - If `div_lt_div_of_pos_left` failed, don't try `div_lt_div_of_pos_left'`
- ❌ **Debugging in-loop** - If Lean error is "unknown identifier", don't guess - bail out

### ⛔ BAIL OUT TRIGGERS (Request Decomposition Instead)

**Stop immediately and set `needs_decomposition` if:**

1. **Unknown lemma error** - "unknown identifier 'foo'" means lemma doesn't exist. Don't guess alternatives.
2. **Type mismatch on core approach** - If your mathematical approach is wrong (not just syntax), bail out.
3. **Same error twice** - If attempt 2 hits the same error class as attempt 1, the approach is wrong.
4. **Complex inequality** - If goal needs 5+ intermediate steps, it should be decomposed further.

```bash
# Example: bail out on repeated type mismatch
if echo "$ERROR" | grep -aq "type mismatch\|could not unify"; then
  if [ "$PREV_ERROR_CLASS" = "type_mismatch" ]; then
    # Same error class twice - bail out
    $E update_memory '{"key_name":"proofs/'$TID'/goals/'$GID'/status","value":"needs_decomposition"}'
    exit 0
  fi
  PREV_ERROR_CLASS="type_mismatch"
fi
```

**CORRECT FLOW:**
1. Math reasoning: WHY does this hold?
2. Targeted search: WHAT lemmas encode this insight?
3. Use results: nlinarith [found_lemma1, found_lemma2]

**WRONG FLOW:**
1. exact? (expensive, blind)
2. apply? (expensive, blind)
3. try random tactics
4. waste tokens

### Recording Attempts (⛔ MANDATORY - DO NOT SKIP)

**Every failed tactic MUST be recorded to Ensue IMMEDIATELY after failure:**

```bash
# Record the failed attempt - THIS IS NOT OPTIONAL
ATTEMPT_NUM=$(date +%s)  # or use counter
$E create_memory "{\"items\":[{
  \"key_name\":\"proofs/$THEOREM_ID/goals/$GOAL_ID/attempts/attempt-$ATTEMPT_NUM\",
  \"value\":\"{\\\"tactic\\\":\\\"$TACTIC\\\",\\\"error\\\":\\\"$ERROR\\\",\\\"agent\\\":\\\"prover-$SID\\\"}\",
  \"description\":\"verification attempt\",
  \"embed\":false
}]}"
```

**WHY THIS MATTERS:**
- Other agents (or your next iteration) won't waste tokens trying the same thing
- The collective intelligence learns from failures
- We can track which approaches have been exhausted

**FAILURE TO RECORD = TOKEN BURN for future agents**

### On Success - VERIFY BEFORE RECORDING

**⚠️ NEVER record a solution without confirming it compiles!**

**⚠️ SOLUTION FORMAT REQUIREMENTS:**
- Use `--` for ALL comments (not bare text)
- No references to undefined helpers (inline everything)
- Calc chains must have `_` on new lines with proper indentation
- Bullets `·` must be inside a `by` block

**⚠️ FILENAME REQUIREMENT: Use `/tmp/verify_{GOAL_ID}.lean`**
This enables automatic attempt tracking. The hook will block after 3 failures.

### Lazy Verification (Skip simple tactics)

**SKIP verification for these tactics** (they always work if goal type is correct):
- `native_decide`, `decide`, `rfl`
- `norm_num`, `ring`, `omega`
- `simp`, `simp only [...]`
- `trivial`, `exact?` results

**VERIFY only complex tactics:**
- `nlinarith [hints]`, `linarith [hints]`
- `calc` chains
- Multi-step tactics with `<;>` or `;`
- Custom lemma applications

```bash
GID="your-goal-id"
TACTIC="norm_num"  # or your tactic

# Check if tactic needs verification
case "$TACTIC" in
  native_decide|decide|rfl|norm_num|ring|omega|trivial)
    # SKIP - trust these simple tactics
    echo "Skipping verification for simple tactic: $TACTIC"
    ;;
  simp|"simp only"*)
    # SKIP - simp usually works
    echo "Skipping verification for simp"
    ;;
  *)
    # VERIFY - complex tactic
    cat > "/tmp/verify_${GID}.lean" << EOF
import Mathlib.Tactic
theorem check : $GOAL_TYPE := by
  $TACTIC
EOF
    cd /private/tmp/putnam-test && lake env lean "/tmp/verify_${GID}.lean" 2>&1
    COMPILE_RESULT=$?
    ;;
esac
```

# Step 3: Only record if compilation succeeded!
if [ $COMPILE_RESULT -eq 0 ]; then
  $E create_memory '{"items":[{"key_name":"proofs/{TID}/solutions/{GID}","value":"{TACTIC}","description":"solution","embed":true}]}'
  $E update_memory '{"key_name":"proofs/{TID}/goals/{GID}/status","value":"solved"}'
else
  echo "TACTIC FAILED COMPILATION - recording as attempt, not solution"
  # Record as failed attempt instead
fi
```

**If it doesn't compile, it's NOT a solution. Debug or try another tactic.**

### ⚠️ REPAIR MODE (When Asked to Fix Errors)

**If you're asked to fix errors in a composed proof, follow this protocol:**

1. **Do NOT edit the composed .lean file** - it will be overwritten
2. **Trace error to source goal:**
   ```bash
   # Get the error line number, then find which goal's solution contains that code
   $E get_memory '{"key_names":["proofs/{TID}/solutions/{SUSPECTED_GOAL}"]}'
   ```
3. **Fix the source solution:**
   - Write a verified fix using the pattern above
   - Store the fix to Ensue
4. **Re-compose:**
   ```bash
   ./scripts/compose-proof.sh {TID}
   ```

**Common fixes:**
- `unknown identifier 'foo'` → Replace with Mathlib equivalent or inline the helper
- `expected ':='` → Add `--` before comments
- `type mismatch` → Check lemma signature with `#check @lemma_name`

### 📚 CONTRIBUTE TO COLLECTIVE INTELLIGENCE (MANDATORY)

**After EVERY successful verification, you MUST contribute to the tactics library:**

```bash
# Step 1: Categorize the tactic
CATEGORY="unknown"
case "$TACTIC" in
  *nlinarith*|*linarith*) CATEGORY="arithmetic" ;;
  *ConcaveOn*|*ConvexOn*|*concave*) CATEGORY="concavity" ;;
  *sin*|*cos*|*Real.pi*) CATEGORY="trigonometry" ;;
  *ring*|*field_simp*) CATEGORY="algebra" ;;
  *simp*|*norm_num*) CATEGORY="simplification" ;;
  *intro*|*constructor*|*rcases*) CATEGORY="structural" ;;
  *exact*|*apply*) CATEGORY="application" ;;
esac

# Step 2: Create a hash for uniqueness
TACTIC_HASH=$(echo "$TACTIC" | md5 | cut -c1-8)

# Step 3: Store in tactics library with goal pattern
$E create_memory "{\"items\":[{
  \"key_name\":\"proofs/$TID/tactics/library/$CATEGORY/$TACTIC_HASH\",
  \"value\":\"{\\\"tactic\\\":\\\"$TACTIC\\\",\\\"goal_pattern\\\":\\\"$GOAL_TYPE\\\",\\\"lemmas_used\\\":[],\\\"agent\\\":\\\"prover-$SID\\\"}\",
  \"description\":\"$CATEGORY tactic for $GOAL_TYPE\",
  \"embed\":true
}]}"
```

**Example - after proving `sin x ≤ f(x)`:**
```bash
$E create_memory '{"items":[{
  "key_name":"proofs/putnam-2025-a2/tactics/library/concavity/a3f8b2c1",
  "value":"{\"tactic\":\"exact strictConcaveOn_sin_Icc.concaveOn.le_right_of_left_le h1 h2\",\"goal_pattern\":\"Real.sin x ≤ _\",\"lemmas_used\":[\"strictConcaveOn_sin_Icc\",\"ConcaveOn.le_right_of_left_le\"]}",
  "description":"concavity tactic for sin upper bound",
  "embed":true
}]}'
```

**WHY THIS MATTERS:**
- Future agents search `tactics/library/` before attempting goals
- Similar goal patterns → similar tactics work
- The collective gets smarter with each solved goal
- Prevents re-discovery of the same approach

**FAILURE TO CONTRIBUTE = WASTED COLLECTIVE LEARNING**

---

### On 3 Failures - REQUEST DECOMPOSITION

**⚠️ CRITICAL: Set `needs_decomposition`, NOT `open`!**

Setting `"open"` creates a loop where another prover gets spawned. Use `"needs_decomposition"` to signal the skill to spawn a decomposer.

```bash
$E update_memory '{"key_name":"proofs/{TID}/goals/{GID}/status","value":"needs_decomposition"}'
# Exit - skill will see this status and spawn a DECOMPOSER (not another prover)
```

**Also record WHY decomposition is needed:**
```bash
$E create_memory '{"items":[{
  "key_name":"proofs/{TID}/goals/{GID}/decomposition_request",
  "value":"{\"reason\":\"verification failed after 3 attempts\",\"suggestion\":\"try case split or concavity argument\"}",
  "description":"decomposition request",
  "embed":true
}]}'
```

### Allowed Tactics (choose based on goal type)

**For inequalities with discovered lemmas:**
- `nlinarith [lemma1, lemma2]` - nonlinear arithmetic with hints
- `linarith [lemma1, lemma2]` - linear arithmetic with hints

**For decidable/numeric goals:**
- `native_decide` - decidable propositions
- `norm_num` - numeric goals
- `decide` - decidable goals

**For algebraic manipulation:**
- `ring` - ring equalities
- `field_simp` - clear denominators
- `simp [lemma]` - with specific lemmas

**For structure:**
- `constructor` - split conjunctions/structures
- `intro` - introduce hypotheses
- `rcases` - case analysis

**ONLY as last resort (expensive):**
- `exact?` - brute force search
- `apply?` - brute force search

### ❌ NEVER DO
- Skip mathematical reasoning
- Use exact?/apply? before targeted search
- Ignore lemmas found by collective intelligence
- Run `grep` on Mathlib source
- Try more than 3 tactics without recording

## MODE B: DECOMPOSE (root and complex goals)

**This is the priority. Decompose creates parallelism.**

```bash
# Claim
$E update_memory '{"key_name":"proofs/{TID}/goals/{GID}/status","value":"working:prover-$SID"}'

# Create subgoals
$E create_memory '{"items":[
  {"key_name":"proofs/{TID}/goals/{SUB1}/definition","value":"{...}","description":"subgoal","embed":true},
  {"key_name":"proofs/{TID}/goals/{SUB1}/status","value":"open","description":"status","embed":false},
  {"key_name":"proofs/{TID}/goals/{SUB1}/parent","value":"{GID}","description":"parent","embed":false},
  ...
]}'

# Mark decomposed with tactic
$E update_memory '{"key_name":"proofs/{TID}/goals/{GID}/status","value":"decomposed"}'
$E update_memory '{"key_name":"proofs/{TID}/goals/{GID}/tactic","value":"constructor"}'
$E update_memory '{"key_name":"proofs/{TID}/goals/{GID}/children","value":"[\"sub1\",\"sub2\"]"}'
```

**IsLeast decomposes to:** membership + minimality (tactic: `constructor`)

## MODE C: COMPOSE (when all done)

Use the compose script when `next-action.sh` returns `{"action":"compose"}`:

```bash
"$SCRIPTS/compose-proof.sh" "$TID"
```

This recursively walks the tree and combines tactics into the final proof.

## AFTER PROVING - REFRESH AND EXIT

After solving or marking needs_decomposition, refresh subscriptions and exit:
```bash
# Refresh subscriptions so status changes trigger notifications
"$SCRIPTS/refresh-subscriptions.sh" "$TID" > /dev/null 2>&1 &

# Exit - the skill will spawn new agents for remaining goals
echo "Finished with $GID. Exiting."
exit 0
```

**EXIT after your ONE goal. The skill spawns new agents for new goals.**

## ⛔ DO NOT (TOKEN EFFICIENCY)

- ❌ **Guess lemma names** - Query Ensue or use `exact?`
- ❌ **Run grep/find/Glob on files** - ALL KNOWLEDGE IS IN ENSUE
- ❌ **Try more than 3 tactics** - Record failure and release goal
- ❌ **Write `#check` to explore** - Query collective intelligence
- ❌ **Use Search, Glob, or Grep tools** - QUERY ENSUE INSTEAD
- ❌ **Search .lake or Mathlib directories** - USE `$E search_memories`
- ❌ **Exit before recording** - Always record attempt/solution to Ensue
- ❌ **Skip decomposition for complex goals** - If it has ∀, ∃, →, decompose first

**The collective intelligence (Ensue) is your knowledge base. Query it, don't search files.**
