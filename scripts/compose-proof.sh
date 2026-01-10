#!/usr/bin/env bash
# compose-proof.sh - Recursively compose a proof tree from Ensue
# Usage: ./compose-proof.sh <theorem_id>

TID="${1:-putnam-2025-a2}"
E="$(find ~/.claude/plugins/cache -name 'ensue-api.sh' -path '*/ensue-memory/*' 2>/dev/null | head -1)"

if [ -z "$E" ]; then
  echo "Error: ensue-api.sh not found"
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

# Get solution for a goal
get_solution() {
  local goal="$1"
  get_value "proofs/$TID/solutions/$goal"
}

# Store composed solution
store_solution() {
  local goal="$1"
  local solution="$2"
  # Escape for JSON
  local escaped
  escaped=$(printf '%s' "$solution" | jq -Rs '.')
  "$E" create_memory "{\"items\":[{\"key_name\":\"proofs/$TID/solutions/$goal\",\"value\":$escaped,\"description\":\"composed solution\",\"embed\":false}]}" >/dev/null 2>&1
}

echo "=== Composing proof for: $TID ==="
echo ""

# Fetch all goal names
echo "Fetching goal tree..."
"$E" list_keys "{\"prefix\":\"proofs/$TID/goals/\",\"limit\":2000}" 2>/dev/null | \
  jq -r '.result.structuredContent.keys[]?.key_name' | \
  grep '/status$' | \
  sed "s|proofs/$TID/goals/||; s|/status$||" | \
  sort -u > "$TMPDIR/goals.txt"

num_goals=$(wc -l < "$TMPDIR/goals.txt" | tr -d ' ')
echo "Found $num_goals goals"

# Cache goal data
echo "Caching goal data..."
cached_with_sol=0
while read -r goal; do
  get_value "proofs/$TID/goals/$goal/status" > "$TMPDIR/$goal.status"
  get_value "proofs/$TID/goals/$goal/tactic" > "$TMPDIR/$goal.tactic"
  get_value "proofs/$TID/goals/$goal/children" > "$TMPDIR/$goal.children"
  sol=$(get_solution "$goal")
  if [ -n "$sol" ]; then
    echo "$sol" > "$TMPDIR/$goal.solution"
    touch "$TMPDIR/$goal.composed"
    cached_with_sol=$((cached_with_sol + 1))
  fi
done < "$TMPDIR/goals.txt"
echo "Cached $cached_with_sol goals with solutions"

echo "Starting composition..."
echo ""

# Iteratively compose
max_iterations=20
iteration=0
total_composed=0

while [ $iteration -lt $max_iterations ]; do
  iteration=$((iteration + 1))
  composed_this_round=0

  while read -r goal; do
    # Skip if already composed
    [ -f "$TMPDIR/$goal.composed" ] && continue

    # DEBUG: Check left-h-pos-intro specifically
    DEBUG_GOAL=""
    [ "$goal" = "left-h-pos-intro" ] && DEBUG_GOAL="1"

    # Get children
    children_json=$(cat "$TMPDIR/$goal.children" 2>/dev/null)

    if [ -n "$DEBUG_GOAL" ]; then
      echo "  DEBUG $goal: children_json='${children_json:0:60}...'"
    fi

    [ -z "$children_json" ] || [ "$children_json" = "null" ] || [ "$children_json" = "[]" ] && continue

    # Parse children into file (one per line)
    echo "$children_json" | jq -r '.[]' 2>/dev/null > "$TMPDIR/current_children.txt"

    if [ -n "$DEBUG_GOAL" ]; then
      echo "  DEBUG $goal: children file has $(wc -l < "$TMPDIR/current_children.txt") lines"
    fi

    [ ! -s "$TMPDIR/current_children.txt" ] && continue

    # Check if all children are composed (skip abandoned/invalid ones)
    all_ready=true
    while IFS= read -r child; do
      [ -z "$child" ] && continue
      # Check if child is abandoned/invalid (can be skipped)
      child_status=$(cat "$TMPDIR/$child.status" 2>/dev/null)
      case "$child_status" in
        abandoned*|invalid*|replaced*|duplicate*|alternative*)
          # Skip this child - it's a dead end
          continue
          ;;
      esac
      if [ ! -f "$TMPDIR/$child.composed" ]; then
        if [ -n "$DEBUG_GOAL" ]; then
          echo "  DEBUG $goal: child '$child' not composed (status: $child_status)"
        fi
        all_ready=false
        break
      fi
    done < "$TMPDIR/current_children.txt"

    if [ -n "$DEBUG_GOAL" ]; then
      echo "  DEBUG $goal: all_ready=$all_ready"
    fi

    [ "$all_ready" = "false" ] && continue

    # Get tactic
    tactic=$(cat "$TMPDIR/$goal.tactic" 2>/dev/null)
    [ "$tactic" = "null" ] && tactic=""

    # Collect child solutions (skip abandoned/invalid)
    child_sols=""
    num_children=0
    while IFS= read -r child; do
      [ -z "$child" ] && continue
      # Skip abandoned/invalid children
      child_status=$(cat "$TMPDIR/$child.status" 2>/dev/null)
      case "$child_status" in
        abandoned*|invalid*|replaced*|duplicate*|alternative*)
          continue
          ;;
      esac
      child_sol=$(cat "$TMPDIR/$child.solution" 2>/dev/null)
      if [ $num_children -gt 0 ]; then
        child_sols+=$'\n'"  · $child_sol"
      else
        child_sols="$child_sol"
      fi
      num_children=$((num_children + 1))
    done < "$TMPDIR/current_children.txt"

    # Format composed solution
    if [ $num_children -eq 1 ]; then
      if [ -n "$tactic" ]; then
        composed="$tactic; $child_sols"
      else
        composed="$child_sols"
      fi
    else
      # Multiple children - use bullets
      if [ -n "$tactic" ]; then
        composed="$tactic"$'\n'"  · ${child_sols}"
      else
        composed="$child_sols"
      fi
    fi

    # Store
    echo "$composed" > "$TMPDIR/$goal.solution"
    touch "$TMPDIR/$goal.composed"
    store_solution "$goal" "$composed"

    echo "  ✓ Composed: $goal"
    composed_this_round=$((composed_this_round + 1))
    total_composed=$((total_composed + 1))

  done < "$TMPDIR/goals.txt"

  echo "Iteration $iteration: composed $composed_this_round goals"

  [ $composed_this_round -eq 0 ] && break
done

echo ""
echo "=== Composition Complete ==="
echo "Composed $total_composed goals in $iteration iterations"
echo ""

# Check root
if [ -f "$TMPDIR/root.solution" ]; then
  echo "✓ Root solution exists!"

  # Fast syntax lint (0.03s vs 0.8s for full Lean)
  SCRIPT_DIR="$(dirname "$0")"
  if [ -f "$SCRIPT_DIR/lint-lean.sh" ]; then
    # Create temp file with proper wrapper
    cat > "$TMPDIR/final_proof.lean" << EOF
import Mathlib

theorem composed_proof : sorry := by
$(cat "$TMPDIR/root.solution" | sed 's/^/  /')
EOF
    echo ""
    echo "--- Fast Syntax Check ---"
    if "$SCRIPT_DIR/lint-lean.sh" "$TMPDIR/final_proof.lean"; then
      echo "✓ Syntax OK (use 'lake env lean' for full verification)"
    else
      echo "✗ Syntax issues found - check above"
    fi
  fi

  echo ""
  echo "--- Final Proof (first 50 lines) ---"
  head -50 "$TMPDIR/root.solution"
else
  echo "✗ Root not composed. Uncomposed goals:"
  while read -r goal; do
    if [ ! -f "$TMPDIR/$goal.composed" ]; then
      status=$(cat "$TMPDIR/$goal.status" 2>/dev/null)
      children=$(cat "$TMPDIR/$goal.children" 2>/dev/null)
      echo "  - $goal (status: $status, children: ${children:0:50})"
    fi
  done < "$TMPDIR/goals.txt" | head -20
fi
