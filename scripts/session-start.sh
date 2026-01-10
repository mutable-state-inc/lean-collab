#!/bin/bash
# Session start hook for lean-collab plugin
# Detects proof session and starts background indexing

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CONFIG_FILE="$PWD/.lean-collab.json"

# Start Mathlib indexer in background (populates collective intelligence)
# Disabled: spawns multiple Lean processes on startup
# Run manually with: ./scripts/index-mathlib.sh <project_dir>
# if [[ -x "$SCRIPT_DIR/index-mathlib.sh" ]]; then
#     nohup "$SCRIPT_DIR/index-mathlib.sh" "$PWD" --background >/dev/null 2>&1 &
#     disown
# fi

if [[ ! -f "$CONFIG_FILE" ]]; then
  exit 0
fi

THEOREM_ID=$(python3 -c "import sys,json; print(json.load(open('$CONFIG_FILE')).get('theorem_id',''))" 2>/dev/null)

if [[ -n "$THEOREM_ID" ]]; then
  echo "lean-collab: Active proof session detected: $THEOREM_ID"
  echo "lean-collab: Collective intelligence indexing in background"
fi

exit 0
