#!/usr/bin/env bash
# validate-solutions.sh - Validate all solutions in Ensue compile correctly
# Usage: ./validate-solutions.sh <theorem_id> [project_dir]
#
# This script checks each solution in Ensue and reports which ones fail to compile.
# Use this to identify broken goals before or after composition.

set -e

TID="${1:-putnam-2025-a2}"
PROJECT_DIR="${2:-/private/tmp/putnam-test}"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
E="$SCRIPT_DIR/ensue-api.sh"

if [ ! -f "$E" ]; then
  echo "Error: ensue-api.sh not found at $E"
  exit 1
fi

TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

# Helper: get a single value from Ensue
get_value() {
  local key="$1"
  "$E" get_memory "{\"key_names\":[\"$key\"]}" 2>/dev/null | \
    jq -r '.result.structuredContent.results[0].value // empty'
}

echo "=== Validating solutions for: $TID ==="
echo "Project: $PROJECT_DIR"
echo ""

# Fetch all solution keys
echo "Fetching solutions..."
"$E" list_keys "{\"prefix\":\"proofs/$TID/solutions/\",\"limit\":500}" 2>/dev/null | \
  jq -r '.result.structuredContent.keys[]?.key_name' | \
  sed "s|proofs/$TID/solutions/||" | \
  sort -u > "$TMPDIR/solutions.txt"

num_solutions=$(wc -l < "$TMPDIR/solutions.txt" | tr -d ' ')
echo "Found $num_solutions solutions"
echo ""

# Track results
valid=0
invalid=0
skipped=0

while read -r goal; do
  [ -z "$goal" ] && continue

  # Get solution
  solution=$(get_value "proofs/$TID/solutions/$goal")
  if [ -z "$solution" ]; then
    echo "  ⊘ $goal: no solution"
    skipped=$((skipped + 1))
    continue
  fi

  # Get goal type for validation
  goal_def=$(get_value "proofs/$TID/goals/$goal/definition")
  if [ -z "$goal_def" ]; then
    # Might be a composed solution without a direct goal definition
    echo "  ? $goal: no definition (composed?)"
    skipped=$((skipped + 1))
    continue
  fi

  goal_type=$(echo "$goal_def" | jq -r '.type // empty' 2>/dev/null)
  if [ -z "$goal_type" ]; then
    echo "  ? $goal: no type in definition"
    skipped=$((skipped + 1))
    continue
  fi

  # Write verification file
  cat > "$TMPDIR/check.lean" << EOF
import Mathlib

theorem check : $goal_type := by
  $solution
EOF

  # Try to compile
  cd "$PROJECT_DIR" && RESULT=$(lake env lean "$TMPDIR/check.lean" 2>&1)
  EXIT_CODE=$?

  if [ $EXIT_CODE -eq 0 ]; then
    echo "  ✓ $goal"
    valid=$((valid + 1))
  else
    echo "  ✗ $goal"
    # Show first error line
    echo "    └─ $(echo "$RESULT" | grep -m1 'error:' | head -c 80)"
    invalid=$((invalid + 1))

    # Store the error for later inspection
    echo "$RESULT" > "$TMPDIR/errors/$goal.err" 2>/dev/null || true
  fi

done < "$TMPDIR/solutions.txt"

echo ""
echo "=== Validation Complete ==="
echo "Valid:   $valid"
echo "Invalid: $invalid"
echo "Skipped: $skipped"

if [ $invalid -gt 0 ]; then
  echo ""
  echo "Invalid solutions need to be fixed before composition."
  echo "Use the Repair Protocol in SKILL.md to fix each broken goal."
  exit 1
fi

exit 0
