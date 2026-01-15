#!/bin/bash
#
# enforce-routing.sh - Hook to enforce correct agent routing
#
# PreToolUse hook for Task tool - blocks if wrong agent type for goal
# Also implements checkpoint assessment at depth intervals
#

# Log to stderr for visibility
log() {
    echo "[enforce-routing] $1" >&2
}

# Read the hook input from stdin
INPUT=$(cat)

# Extract tool input
TOOL_INPUT=$(echo "$INPUT" | jq -r '.tool_input // empty')
if [ -z "$TOOL_INPUT" ]; then
    echo '{"decision":"approve"}'
    exit 0
fi

# Get subagent_type
SUBAGENT_TYPE=$(echo "$TOOL_INPUT" | jq -r '.subagent_type // empty')

# Only check lean-collab routing
case "$SUBAGENT_TYPE" in
    lean-collab:decomposer|lean-collab:lean-prover)
        ;;
    *)
        echo '{"decision":"approve"}'
        exit 0
        ;;
esac

# Extract goal ID from prompt
PROMPT=$(echo "$TOOL_INPUT" | jq -r '.prompt // empty')

# Extract goal ID - patterns: "goal isGreatest-mem" or "Decompose goal isGreatest-mem"
# The goal ID follows "goal " in the prompt
GOAL_ID=$(echo "$PROMPT" | grep -oE 'goal [a-zA-Z0-9_-]+' | head -1 | sed 's/goal //')

if [ -z "$GOAL_ID" ]; then
    echo '{"decision":"approve"}'
    exit 0
fi

# Get plugin path from .lean-collab.json
PLUGIN_PATH=$(cat .lean-collab.json 2>/dev/null | jq -r '.plugin_path // empty')
if [ -z "$PLUGIN_PATH" ]; then
    # Fallback to script directory
    PLUGIN_PATH="$(cd "$(dirname "$0")/.." && pwd)"
fi

# Get theorem ID from prompt
TID=$(echo "$PROMPT" | grep -oE 'putnam-[a-zA-Z0-9_-]+' | head -1)
if [ -z "$TID" ]; then
    TID=$(cat .lean-collab.json 2>/dev/null | jq -r '.theorem_id // empty')
fi

if [ -z "$TID" ]; then
    echo '{"decision":"approve"}'
    exit 0
fi

E="$PLUGIN_PATH/scripts/ensue-api.sh"

# CHECKPOINT ASSESSMENT: At depths divisible by (MAX_DEPTH/4), assess complexity
# Only for decomposer calls - ask the model if goal is simple enough to prove directly
if [ "$SUBAGENT_TYPE" = "lean-collab:decomposer" ]; then
    # Get MAX_DEPTH: env var > config file > default
    MAX_DEPTH="${LEAN_COLLAB_MAX_DEPTH:-}"
    if [ -z "$MAX_DEPTH" ] && [ -f ".lean-collab.json" ]; then
        MAX_DEPTH=$(cat .lean-collab.json 2>/dev/null | jq -r '.max_depth // empty')
    fi
    MAX_DEPTH="${MAX_DEPTH:-35}"

    # Fetch goal definition to get depth and type
    GOAL_DATA=$("$E" get_memory "{\"key_names\":[\"proofs/$TID/goals/$GOAL_ID/definition\",\"proofs/$TID/goals/$GOAL_ID/depth\"]}" 2>/dev/null)
    GOAL_DEF=$(echo "$GOAL_DATA" | jq -r '.result.structuredContent.results[0].value // "{}"')
    GOAL_DEPTH=$(echo "$GOAL_DATA" | jq -r '.result.structuredContent.results[1].value // "0"')

    # Parse depth (handle both raw number and JSON)
    if echo "$GOAL_DEPTH" | grep -q '{'; then
        GOAL_DEPTH=$(echo "$GOAL_DEPTH" | jq -r '.depth // 0')
    fi
    GOAL_DEPTH=${GOAL_DEPTH:-0}

    # Calculate checkpoint interval (every 1/16 of max depth = ~2 depths)
    CHECKPOINT_INTERVAL=$((MAX_DEPTH / 16))
    [ "$CHECKPOINT_INTERVAL" -lt 1 ] && CHECKPOINT_INTERVAL=1

    # Check if at checkpoint depth
    if [ "$GOAL_DEPTH" -gt 0 ] && [ "$((GOAL_DEPTH % CHECKPOINT_INTERVAL))" -eq 0 ]; then
        # Skip if already assessed (marker in prompt or in memory)
        if echo "$PROMPT" | grep -q '\[ASSESSED_COMPLEX\]'; then
            # Model already assessed as complex, allow decomposition
            :
        else
            # Check if checkpoint was already assessed in memory
            ASSESSED=$("$E" get_memory "{\"key_names\":[\"proofs/$TID/goals/$GOAL_ID/checkpoint_assessed\"]}" 2>/dev/null | jq -r '.result.structuredContent.results[0].value // empty')
            if [ -n "$ASSESSED" ] && [ "$ASSESSED" != "null" ]; then
                # Already assessed, skip checkpoint
                :
            else
                # Extract goal type for assessment
                GOAL_TYPE=$(echo "$GOAL_DEF" | jq -r '.type // empty')
                [ -z "$GOAL_TYPE" ] && GOAL_TYPE="$GOAL_DEF"

                # Block and ask model to assess
                log "CHECKPOINT @ depth $GOAL_DEPTH: $GOAL_ID - needs complexity assessment"
                cat << ENDJSON
{
  "decision": "block",
  "reason": "CHECKPOINT_ASSESSMENT",
  "goal": "$GOAL_ID",
  "depth": $GOAL_DEPTH,
  "message": "⏸️ CHECKPOINT (depth $GOAL_DEPTH): Assess '$GOAL_ID' before decomposing.\n\nGoal: $GOAL_TYPE\n\n→ SIMPLE? Use lean-prover instead\n→ COMPLEX? Add [ASSESSED_COMPLEX] to prompt and retry"
}
ENDJSON
                exit 0
            fi
        fi
    fi
fi

# LEAF VALIDATION: When prover is called, check if goal is actually simple enough
if [ "$SUBAGENT_TYPE" = "lean-collab:lean-prover" ]; then
    # Get goal info
    GOAL_DATA=$("$E" get_memory "{\"key_names\":[\"proofs/$TID/goals/$GOAL_ID/definition\",\"proofs/$TID/goals/$GOAL_ID/leaf_type\"]}" 2>/dev/null)
    GOAL_DEF=$(echo "$GOAL_DATA" | jq -r '.result.structuredContent.results[0].value // "{}"')
    LEAF_TYPE=$(echo "$GOAL_DATA" | jq -r '.result.structuredContent.results[1].value // empty')
    GOAL_TYPE=$(echo "$GOAL_DEF" | jq -r '.type // empty')

    # Check if "discoverable" goal contains complex patterns that need Mathlib search
    if [ "$LEAF_TYPE" = "discoverable" ]; then
        COMPLEX_PATTERNS="ConcaveOn|ConvexOn|AntitoneOn|MonotoneOn|DifferentiableOn|ContDiffOn|StrictConcaveOn|StrictConvexOn|HasDerivAt|IntervalIntegral|MeasureTheory"
        if echo "$GOAL_TYPE" | grep -qE "$COMPLEX_PATTERNS"; then
            # Block and warn - this needs Mathlib lemma search, not basic tactics
            log "MATHLIB_REQUIRED: $GOAL_ID needs lemma search (type: $LEAF_TYPE)"
            cat << ENDJSON
{
  "decision": "block",
  "reason": "MATHLIB_REQUIRED",
  "goal": "$GOAL_ID",
  "leaf_type": "$LEAF_TYPE",
  "message": "🔬 MATHLIB REQUIRED: '$GOAL_ID' needs lemma lookup.\n\nGoal: $GOAL_TYPE\n\n→ Search: \$E search_memories for relevant lemma\n→ Verify: #check @LemmaName\n→ Apply: exact LemmaName args\n\nAdd [MATHLIB_AWARE] to proceed, or mark needs_decomposition"
}
ENDJSON
            # Allow if already marked as mathlib-aware
            if echo "$PROMPT" | grep -q '\[MATHLIB_AWARE\]'; then
                : # Continue to standard routing
            else
                exit 0
            fi
        fi
    fi

    # Check for universal/existential quantifiers that shouldn't be leaves
    if echo "$GOAL_TYPE" | grep -qE "^∀|^∃|forall|exists"; then
        if ! echo "$PROMPT" | grep -q '\[QUANTIFIER_AWARE\]'; then
            log "QUANTIFIER_LEAF: $GOAL_ID has quantifiers but is marked as leaf"
            cat << ENDJSON
{
  "decision": "block",
  "reason": "QUANTIFIER_LEAF",
  "goal": "$GOAL_ID",
  "message": "⚠️ QUANTIFIER LEAF: '$GOAL_ID' has ∀/∃ but is marked as leaf.\n\nGoal: $GOAL_TYPE\n\n→ Usually needs decomposition (intro, cases)\n→ Add [QUANTIFIER_AWARE] if basic tactics work\n→ Or mark needs_decomposition"
}
ENDJSON
            exit 0
        fi
    fi
fi

# Run route-goal.sh for standard routing check
CORRECT_ROUTE=$("$PLUGIN_PATH/scripts/route-goal.sh" "$TID" "$GOAL_ID" 2>/dev/null)

if [ -z "$CORRECT_ROUTE" ]; then
    echo '{"decision":"approve"}'
    exit 0
fi

# Check if routing matches
REQUESTED_AGENT=""
case "$SUBAGENT_TYPE" in
    lean-collab:decomposer) REQUESTED_AGENT="decomposer" ;;
    lean-collab:lean-prover) REQUESTED_AGENT="prover" ;;
esac

if [ "$CORRECT_ROUTE" != "$REQUESTED_AGENT" ]; then
    log "WRONG_ROUTE: $GOAL_ID → should be $CORRECT_ROUTE, not $REQUESTED_AGENT"
    cat << ENDJSON
{
  "decision": "block",
  "reason": "WRONG_ROUTE",
  "goal": "$GOAL_ID",
  "expected": "$CORRECT_ROUTE",
  "requested": "$REQUESTED_AGENT",
  "message": "🚫 WRONG ROUTE: '$GOAL_ID' → use $CORRECT_ROUTE, not $REQUESTED_AGENT"
}
ENDJSON
    exit 0
fi

log "APPROVED: $GOAL_ID → $REQUESTED_AGENT"
echo '{"decision":"approve"}'
