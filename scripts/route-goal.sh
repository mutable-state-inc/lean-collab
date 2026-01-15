#!/bin/bash
#
# route-goal.sh - Deterministic routing for goals
#
# Usage: ./route-goal.sh <theorem_id> <goal_id>
#
# Output: "decomposer" or "prover"
#
# Logic (in order):
#   1. depth >= MAX_DEPTH → prover (forced, no more decomposition)
#   2. depth < MAX_DEPTH / 2 → decomposer (first half always decomposes)
#   3. Has ∀, ∃, →, forall, exists → decomposer (need intro)
#   4. Has transcendental AND depth < MAX_DEPTH - 3 → decomposer
#   5. Has leaf_type set → prover (decomposer already marked it)
#   6. Default → prover

TID="${1:-}"
GOAL_ID="${2:-}"

if [ -z "$TID" ] || [ -z "$GOAL_ID" ]; then
    echo "error: Usage: route-goal.sh <theorem_id> <goal_id>" >&2
    exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
E="$SCRIPT_DIR/ensue-api.sh"

# Get MAX_DEPTH from config
MAX_DEPTH=25
if [ -f ".lean-collab.json" ]; then
    CONFIGURED=$(cat .lean-collab.json 2>/dev/null | jq -r '.max_depth // empty')
    [ -n "$CONFIGURED" ] && MAX_DEPTH="$CONFIGURED"
fi

# Fetch goal definition and leaf_type in one call
RESULT=$("$E" get_memory "{\"key_names\":[\"proofs/$TID/goals/$GOAL_ID/definition\",\"proofs/$TID/goals/$GOAL_ID/leaf_type\"]}" 2>/dev/null)

GOAL_DEF=$(echo "$RESULT" | jq -r '.result.structuredContent.results[0].value // "{}"')
LEAF_TYPE=$(echo "$RESULT" | jq -r '.result.structuredContent.results[1].value // empty')

GOAL_TYPE=$(echo "$GOAL_DEF" | jq -r '.type // ""')
GOAL_DEPTH=$(echo "$GOAL_DEF" | jq -r '.depth // 0')

# Step 1: If at max depth, must prove (no more decomposition allowed)
if [ "$GOAL_DEPTH" -ge "$MAX_DEPTH" ]; then
    echo "prover"
    exit 0
fi

# Step 2: First half of tree → always decompose (maximize parallelism)
HALF_DEPTH=$((MAX_DEPTH / 2))
if [ "$GOAL_DEPTH" -lt "$HALF_DEPTH" ]; then
    echo "decomposer"
    exit 0
fi

# Step 3: QUANTIFIER CHECK (the main gate for decomposition)
if echo "$GOAL_TYPE" | grep -qE '∀|∃|→|forall|exists'; then
    echo "decomposer"
    exit 0
fi

# Step 4: TRANSCENDENTAL CHECK - decompose unless very deep
# Only send to prover if depth >= MAX_DEPTH - 3 (last 3 levels)
if echo "$GOAL_TYPE" | grep -qE 'Real\.sin|Real\.cos|Real\.exp|Real\.log|Real\.pi|\.sin|\.cos'; then
    PROVER_THRESHOLD=$((MAX_DEPTH - 3))
    if [ "$GOAL_DEPTH" -lt "$PROVER_THRESHOLD" ]; then
        echo "decomposer"
        exit 0
    fi
fi

# Step 5: If leaf_type is set, decomposer already analyzed it
if [ -n "$LEAF_TYPE" ] && [ "$LEAF_TYPE" != "null" ]; then
    echo "prover"
    exit 0
fi

# Step 6: Default → prover
echo "prover"
