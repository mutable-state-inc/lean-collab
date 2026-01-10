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

if [[ ! -f "$PROJECT_DIR/lakefile.lean" ]]; then
    echo "Error: No lakefile.lean in $PROJECT_DIR" >&2
    exit 2
fi

# Create temp directory
VERIFY_DIR=$(mktemp -d)
trap "rm -rf $VERIFY_DIR" EXIT

# Build hypothesis declarations from JSON
HYPOTHESIS_DECLS=""
if [[ "$HYPOTHESES" != "[]" && "$HYPOTHESES" != "" ]]; then
    # Parse JSON and convert to Lean variable declarations
    # Format: [{"name": "n", "type": "Nat"}, {"name": "ih", "type": "n + m = m + n"}]
    HYPOTHESIS_DECLS=$(echo "$HYPOTHESES" | python3 -c "
import json, sys
hyps = json.load(sys.stdin)
for h in hyps:
    name = h.get('name', '_')
    htype = h.get('type', 'True')
    print(f'variable ({name} : {htype})')
" 2>/dev/null || echo "")
fi

# Create verification file
cat > "$VERIFY_DIR/Check.lean" << EOF
import Mathlib.Tactic

$HYPOTHESIS_DECLS

theorem _check_goal : $GOAL_TYPE := by
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
