#!/bin/bash
# Setup script for lean-collab plugin
# Installs leantree and builds the Lean REPL

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PLUGIN_ROOT="$(dirname "$SCRIPT_DIR")"

echo "Installing leantree..."
pip install -e "$PLUGIN_ROOT/../leantree"

echo "Building Lean REPL..."
cd "$PLUGIN_ROOT/../leantree/lean-repl"
lake build

echo "Setup complete!"
echo ""
echo "To start a proof session:"
echo "  1. Create .lean-collab.json with {\"theorem_id\": \"your-theorem\"}"
echo "  2. Run: claude"
