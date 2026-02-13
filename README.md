# lean-collab

Multi-agent collaborative theorem proving with Lean 4 and Ensue Memory Network.

**[Read the blog post](https://ensue.dev/blog/stop-throwing-a-single-agent-at-complex-problems/)**

## Prerequisites

### Lean 4 Installation

Install elan (Lean version manager):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Restart your terminal or source the environment:

```bash
source ~/.elan/env
```

Verify installation:

```bash
lean --version
lake --version
```

### Lean Project with Mathlib

Your Lean project needs Mathlib. For a new project:

```bash
lake new my-project math
cd my-project
```

**Install Mathlib from cache (recommended - saves hours of build time):**

```bash
lake exe cache get
```

Then build:

```bash
lake build
```

For existing projects, add to your `lakefile.lean`:

```lean
require mathlib from git "https://github.com/leanprover-community/mathlib4"
```

Then run:

```bash
lake update
lake exe cache get
lake build
```

### Rust Toolchain

Install Rust:

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

### Ensue API Key

Get an API key from [ensue.dev](https://ensue.dev).

## Setup

### 1. Clone and Build the CLI

```bash
git clone git@github.com:mutable-state-inc/lean-collab.git
cd lean-collab-plugin
make install
```

This compiles the Rust CLI and creates `./bin/lc`.

### 2. Configure Ensue Authentication

```bash
echo "your-ensue-api-key" > .ensue-key
chmod 600 .ensue-key
```

### 3. Configure Local Settings

Create `.lean-collab.json` in the plugin directory:

```json
{
  "theorem_id": "my-theorem",
  "ensue_api_url": "https://api.ensue-network.ai",
  "max_parallel_agents": 7,
  "max_depth": 12,
  "claim_ttl_seconds": 300,
  "lean_project_root": "/absolute/path/to/your/lean/project"
}
```

| Field | Description | Default |
|-------|-------------|---------|
| `theorem_id` | Unique identifier for your proof session | Required |
| `ensue_api_url` | Ensue API endpoint | `https://api.ensue-network.ai` |
| `max_parallel_agents` | Maximum concurrent worker agents | 12 |
| `max_depth` | Maximum proof tree depth | 12 |
| `claim_ttl_seconds` | Goal claim timeout in seconds | 300 |
| `lean_project_root` | Absolute path to your Lean 4 project | Required |

Environment variables override config values:

```bash
export LEAN_COLLAB_MAX_PARALLEL_AGENTS=6
export LEAN_COLLAB_MAX_DEPTH=8
export LEAN_COLLAB_CLAIM_TTL=600
```

## Lean LSP & Verification

The CLI uses `lake env lean` to verify tactics against your Lean project. This requires:

1. A valid `lean_project_root` pointing to a Lean 4 project
2. The project must build successfully with `lake build`
3. Mathlib must be installed (use `lake exe cache get` for speed)

## CLI Reference

### Session Management

```bash
# Initialize and create root goal
./bin/lc init --create-root \
  --theorem "∀ x ∈ [0,π], sin(x) ≥ (2/π)x" \
  --hypotheses "x : ℝ;;hx : x ∈ Set.Icc 0 Real.pi"

# Check proof progress
./bin/lc status                    # Overview of all goals
./bin/lc status <goal_id>          # Details for specific goal

# Stream real-time events
./bin/lc listen --prefix proofs/

# Build final proof when ready
./bin/lc compose
```

### Goal Management

```bash
./bin/lc claim <goal_id>                    # Claim a goal for work
./bin/lc unclaim <goal_id>                  # Release a goal
./bin/lc verify --goal <id> --tactic "..."  # Verify a tactic
./bin/lc verify --goal <id> --tactic "..." --skeleton  # Check types only (allows sorry)
./bin/lc decompose <id> --children X,Y --strategy S
./bin/lc backtrack <id>                     # Undo decomposition
./bin/lc abandon <id>                       # Give up on goal
./bin/lc axiomatize <id> --reason "..."     # Accept as axiom (last resort)
```

### Search & Exploration

```bash
./bin/lc search "query" --prefix tactics/   # Search collective intelligence
./bin/lc explore --goal <id> --tactic "..." # Test tactic interactively
./bin/lc suggest --goal <id>                # Get tactic suggestions
```

## Running with Claude

### 1. Start the Warm Server

Before running Claude, start the warm server in a separate terminal:

```bash
cd /path/to/lean-collab-plugin
./bin/lc warm
```

Keep this terminal open. The warm server:
- Loads Mathlib into memory once (~20s initial load)
- Dramatically speeds up tactic verification (~2-5s vs ~20s per verification)
- Listens on `/tmp/lean-warm.sock`

Without the warm server, each verification cold-starts Lean and reloads Mathlib, which is very slow.

### 2. Start Claude

From the plugin directory (in a new terminal):

```bash
claude \
    --plugin-dir /path/to/lean-collab-plugin \
    --allowedTools "Bash,Read,Write,Edit,Task,Glob,Grep" \
    --dangerously-skip-permissions
```

### 3. Invoke the Skill

Once Claude is running, start the collaborative proving process:

```
Prove that <your theorem statement>.
Use /lean-collab to orchestrate.
```

Example:

```
Prove that for all x in [0, pi], sin(x) >= (2/pi)x.
Use /lean-collab to orchestrate.
```

Claude will:
1. Initialize the proof session with `./bin/lc init`
2. Spawn parallel worker agents (provers and decomposers)
3. Coordinate via Ensue until the proof is complete
4. Compose the final verified Lean proof with `./bin/lc compose`

## Important Disclaimer

**Token Usage Warning:** This tool spawns multiple parallel agents and can consume significant API tokens, especially for complex proofs or when running many workers.

**Recommendations:**

- **Use a Max 20x account** - The parallel agent spawning and iterative proving process burns through tokens quickly. A higher rate limit account is strongly recommended.

- **Monitor in a separate window** - Although lean-collab has been used to solve several problems autonomously, it helps to have another Claude Code window open with the `/lean-collab` skill loaded to monitor progress. This lets you intervene if the solving process becomes tedious or gets stuck in unproductive loops.

- **Start with fewer workers** - Begin with `max_parallel_agents: 3-5` until you're comfortable with token consumption, then scale up.

- **Watch for loops** - If agents are repeatedly backtracking on the same goals, consider manually intervening or adjusting your theorem formulation.

## Author

Sai Vegasena <sai@ensue.dev>
