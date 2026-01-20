# lean-collab

Multi-agent collaborative theorem proving with Lean 4 and Ensue Memory Network.

**[Read the blog post →](https://ensue.dev/blog/stop-throwing-a-single-agent-at-complex-problems/)**

## Quick Start

### 1. Build the CLI

```bash
git clone https://github.com/anthropics/lean-collab-plugin
cd lean-collab-plugin
make install
```

### 2. Configure Ensue

```bash
echo "your-ensue-api-key" > .ensue-key
```

### 3. Configure your Lean project

Create `.lean-collab.json` in the plugin directory:
```json
{
  "theorem_id": "my-theorem",
  "lean_project_root": "/path/to/your/lean/project"
}
```

### 4. Run

```bash
claude \
    --plugin-dir /path/to/lean-collab-plugin \
    --allowedTools "Bash,Read,Write,Edit,Task,Glob,Grep" \
    --dangerously-skip-permissions
```

Then tell Claude:
```
Prove that ∀ x ∈ [0, π], sin(x) ≥ (2/π)x.
Use /lean-collab to orchestrate.
```

## CLI Reference

```bash
lc init --create-root --theorem "..."   # Start proof session
lc status                                # Check progress
lc status <goal_id>                      # Goal details
lc listen                                # Stream events
lc compose                               # Build final proof
```

## Requirements

- Rust toolchain
- Lean 4 with Mathlib
- Ensue API key ([get one](https://ensue.dev))

## Author

Sai Vegasena <sai@ensue.dev>
