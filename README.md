# lean-collab

Multi-agent collaborative theorem proving with LeanTree and Ensue Memory Network.

## Overview

This Claude Code plugin enables multiple Claude sessions to collaboratively solve Lean 4 proofs. Agents coordinate via Ensue's namespaced memory system, with real-time sync through SSE notifications.

**Key features:**
- Any agent can join at any time and immediately understand proof state
- Optimistic goal claiming with timestamp-based conflict resolution
- Failed tactic recording prevents redundant work
- Semantic search finds similar solved goals for tactic suggestions

## Installation

1. Ensure you have an Ensue API key set:
   ```bash
   export ENSUE_API_KEY="your-key-here"
   ```

2. Install the plugin (method TBD based on Claude Code plugin system)

## Quick Start

### Ensue API Script

This plugin depends on `ensue-memory`. Use the ensue-memory plugin's script:
```bash
# Find the ensue-memory plugin script (installed by Claude's plugin system)
ENSUE="$(find ~/.claude/plugins/cache -name 'ensue-api.sh' -path '*/ensue-memory/*' 2>/dev/null | head -1)"
```

Or invoke the `/ensue-memory` skill which handles API calls automatically.

### Start a New Proof Session

Create `.lean-collab.json` in your working directory:
```json
{
  "theorem_id": "nat-add-comm"
}
```

Initialize the proof:
```bash
$ENSUE create_memory '{"items":[
  {"key_name":"proofs/nat-add-comm/_meta/theorem","value":"∀ n m : Nat, n + m = m + n","embed":true},
  {"key_name":"proofs/nat-add-comm/_meta/status","value":"active","embed":false},
  {"key_name":"proofs/nat-add-comm/_meta/goal_index","value":"[\"root\"]","embed":false},
  {"key_name":"proofs/nat-add-comm/goals/root/definition","value":"{\"type\":\"∀ n m : Nat, n + m = m + n\",\"hypotheses\":[]}","embed":true},
  {"key_name":"proofs/nat-add-comm/goals/root/status","value":"open","embed":false}
]}'
```

### Join an Existing Session

Create `.lean-collab.json` pointing to the theorem:
```json
{
  "theorem_id": "nat-add-comm"
}
```

The session-start hook will automatically:
- Register your agent
- Subscribe to goal notifications
- Start the SSE listener

### Claim a Goal

```bash
GOAL_ID="root"
AGENT_ID="claude-$$"
TIMESTAMP=$(date +%s)

# Claim it
$ENSUE update_memory '{"key_name":"proofs/nat-add-comm/goals/'$GOAL_ID'/status","value":"working:'$AGENT_ID':'$TIMESTAMP'"}'

# Verify claim (wait 100ms, re-read)
sleep 0.1
$ENSUE get_memory '{"key_names":["proofs/nat-add-comm/goals/'$GOAL_ID'/status"]}'
```

### Record a Solution

```bash
$ENSUE create_memory '{"items":[{
  "key_name":"proofs/nat-add-comm/solutions/'$GOAL_ID'",
  "value":"induction n with | zero => simp | succ n ih => simp [ih]",
  "embed":true
}]}'

$ENSUE update_memory '{"key_name":"proofs/nat-add-comm/goals/'$GOAL_ID'/status","value":"solved"}'
```

## Namespace Structure

```
proofs/{theorem-id}/
  _meta/
    theorem          # Theorem statement
    status           # active | solved | abandoned
    goal_index       # JSON array of all goal IDs

  goals/
    {goal-id}/
      definition     # Goal type + hypotheses (JSON)
      status         # open | working:{agent}:{timestamp} | solved
      parent         # Parent goal ID
      children       # Child goal IDs after tactic application

  solutions/
    {goal-id}        # Tactic that solved this goal

  attempts/
    {goal-id}/
      {tactic-hash}  # Failed tactic + error message

  agents/
    {agent-id}/
      heartbeat      # Unix timestamp (updated every 30s)
      working-on     # Current goal ID
```

## Claim Protocol

When two agents try to claim the same goal:

1. Both write `working:{self}:{timestamp}` to `goals/{id}/status`
2. Wait 100ms
3. Read back status
4. **Earlier timestamp wins** - if your timestamp is later, back off

## Heartbeat Protocol

Update heartbeat every 30 seconds:
```bash
./scripts/heartbeat.sh <theorem_id> <agent_id>
```

Goals are considered **abandoned** if:
- Status is `working:{agent}:{timestamp}`
- Agent's heartbeat is older than 5 minutes

Other agents can reclaim abandoned goals.

## Scripts

| Script | Purpose |
|--------|---------|
| `ensue-api.sh` | Wrapper for Ensue API calls |
| `listener.sh` | SSE connection for real-time notifications |
| `session-start.sh` | Auto-init on session start |
| `session-end.sh` | Cleanup on session end |
| `heartbeat.sh` | Update agent heartbeat |
| `refresh-subscriptions.sh` | Subscribe to new goal keys |

## Agents

### lean-prover

Specialized subagent for solving Lean goals. Spawn with:
```
Task(subagent_type="lean-prover", prompt="...")
```

Provide context:
- `theorem_id`: The proof session ID
- `goal_id` (optional): Specific goal to work on
- `plugin_root`: Path to plugin scripts

## Real-Time Sync

The plugin uses Ensue's notification service for real-time updates:

1. **Subscribe to keys** - `session-start.sh` subscribes to goal status keys
2. **SSE listener** - `listener.sh` maintains connection, outputs notifications
3. **Refresh subscriptions** - When `goal_index` changes, run `refresh-subscriptions.sh`

## Finding Similar Goals

Use semantic search to find tactics from similar goals:
```bash
./scripts/ensue-api.sh search_memories '{"query":"commutativity natural numbers","prefix":"proofs/","limit":5}'
```

## Author

Sai Vegasena <sai@ensue.dev>
