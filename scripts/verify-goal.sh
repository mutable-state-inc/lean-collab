#!/bin/bash
#
# verify-goal.sh - Verify a goal, but check decomposability FIRST
#
# Usage: verify-goal.sh <project_dir> <goal_type> <tactic> [hypotheses_json]
#
# This script enforces the rule: "Always check decomposability before verification"
#
# Exit codes:
#   0 - Verification succeeded
#   1 - Verification failed
#   3 - DECOMPOSABLE (goal should be decomposed, not verified!)

set -e

PROJECT_DIR="${1:-}"
GOAL_TYPE="${2:-}"
TACTIC="${3:-}"
HYPOTHESES="${4:-[]}"

if [[ -z "$PROJECT_DIR" || -z "$GOAL_TYPE" || -z "$TACTIC" ]]; then
    echo "Usage: verify-goal.sh <project_dir> <goal_type> <tactic> [hypotheses_json]" >&2
    exit 2
fi

SCRIPT_DIR="$(dirname "$0")"

# STEP 1: Check decomposability FIRST
# Try common decomposition tactics
DECOMP_TACTICS=("constructor" "intro x" "intro x hx" "intro h" "cases h" "left" "right")

for DT in "${DECOMP_TACTICS[@]}"; do
    RESULT=$("$SCRIPT_DIR/lean-check.sh" "$PROJECT_DIR" "$GOAL_TYPE" "$DT" "$HYPOTHESES" 2>&1) || continue

    if [[ "$RESULT" == SUBGOALS:* ]]; then
        echo "DECOMPOSABLE: Goal can be decomposed with '$DT'" >&2
        echo "DECOMPOSABLE|$DT|${RESULT#SUBGOALS: }"
        exit 3
    fi

    if [[ "$RESULT" == "VERIFIED" ]]; then
        # Decomposition tactic actually closed the goal!
        echo "VERIFIED (by decomposition tactic: $DT)"
        exit 0
    fi
done

# STEP 2: No decomposition possible, proceed with verification
RESULT=$("$SCRIPT_DIR/lean-check.sh" "$PROJECT_DIR" "$GOAL_TYPE" "$TACTIC" "$HYPOTHESES" 2>&1) || {
    echo "$RESULT" >&2
    exit 1
}

if [[ "$RESULT" == "VERIFIED" ]]; then
    echo "VERIFIED"
    exit 0
elif [[ "$RESULT" == SUBGOALS:* ]]; then
    echo "SUBGOALS: ${RESULT#SUBGOALS: }"
    exit 0
else
    echo "$RESULT" >&2
    exit 1
fi
