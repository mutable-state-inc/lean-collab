#!/bin/bash
#
# lean-check.sh - Verify a tactic in Lean
#
# Usage: lean-check.sh <project_dir> <goal_type> <tactic> [hypotheses_json]
#
# Arguments:
#   project_dir     - Path to Lean project with lakefile.lean
#   goal_type       - The goal type to prove (Lean syntax)
#   tactic          - The tactic to verify
#   hypotheses_json - Optional JSON array of {"name": "...", "type": "..."} objects
#
# Exit codes:
#   0 - Tactic verified successfully
#   1 - Tactic failed (check stderr for error)
#   2 - Usage error
#
# Output:
#   On success: "VERIFIED"
#   On subgoals: "SUBGOALS: <json array of remaining goals>"
#   On failure: Error message from Lean

set -e

PROJECT_DIR="${1:-}"
GOAL_TYPE="${2:-}"
TACTIC="${3:-}"
HYPOTHESES="${4:-[]}"

if [[ -z "$PROJECT_DIR" || -z "$GOAL_TYPE" || -z "$TACTIC" ]]; then
    echo "Usage: lean-check.sh <project_dir> <goal_type> <tactic> [hypotheses_json]" >&2
    exit 2
fi

if [[ ! -f "$PROJECT_DIR/lakefile.lean" && ! -f "$PROJECT_DIR/lakefile.toml" ]]; then
    echo "Error: No lakefile in $PROJECT_DIR" >&2
    exit 2
fi

# Create temp directory
VERIFY_DIR=$(mktemp -d)
trap "rm -rf $VERIFY_DIR" EXIT

# Build hypothesis list for theorem signature
HYPOTHESIS_SIG=""
if [[ "$HYPOTHESES" != "[]" && "$HYPOTHESES" != "" ]]; then
    # Handle two formats:
    # 1. String format: ["x : ℝ", "hx : x ∈ Set.Icc 0 1"] -> (x : ℝ) (hx : x ∈ Set.Icc 0 1)
    # 2. Object format: [{"name": "x", "type": "ℝ"}] -> (x : ℝ)
    HYPOTHESIS_SIG=$(echo "$HYPOTHESES" | python3 -c "
import json, sys
hyps = json.load(sys.stdin)
parts = []
for h in hyps:
    if isinstance(h, str):
        parts.append(f'({h})')
    elif isinstance(h, dict):
        name = h.get('name', '_')
        htype = h.get('type', 'True')
        parts.append(f'({name} : {htype})')
print(' '.join(parts))
" 2>/dev/null || echo "")
fi

# Create verification file
cat > "$VERIFY_DIR/Check.lean" << EOF
import Mathlib.Tactic

theorem _check_goal $HYPOTHESIS_SIG : $GOAL_TYPE := by
  $TACTIC
EOF

# Run Lean
cd "$PROJECT_DIR"
OUTPUT=$(lake env lean "$VERIFY_DIR/Check.lean" 2>&1) || EXIT_CODE=$?
EXIT_CODE=${EXIT_CODE:-0}

if [[ $EXIT_CODE -eq 0 ]]; then
    # Check for unsolved goals warning
    if echo "$OUTPUT" | grep -q "unsolved goals"; then
        # Extract the unsolved goals
        SUBGOALS=$(echo "$OUTPUT" | grep -A 100 "unsolved goals" | tail -n +2 | head -20)
        echo "SUBGOALS: $SUBGOALS"
        exit 0
    else
        echo "VERIFIED"
        exit 0
    fi
else
    # Tactic failed
    echo "$OUTPUT" >&2
    exit 1
fi
