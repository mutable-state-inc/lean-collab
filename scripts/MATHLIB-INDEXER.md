# Mathlib Lemma Indexer

Optional tool that indexes useful Mathlib lemmas into Ensue Memory for semantic search during proof sessions.

## What it does

Extracts theorem/lemma names and type signatures from Mathlib and stores them in Ensue under `tactics/library/`. Agents can then search for relevant lemmas by description rather than needing to know exact names.

Example query:
```
search_memories '{"query":"sin bound concave","prefix":"tactics/library/"}'
```

## Prerequisites

- Ensue Memory plugin installed
- A Lean project with Mathlib in `.lake/packages/mathlib`

## Usage

Run from your Lean project directory:

```bash
# Run indexer (takes a few minutes)
path/to/lean-collab-plugin/scripts/index-mathlib.sh .

# Or run in background
path/to/lean-collab-plugin/scripts/index-mathlib.sh . --background
```

## What gets indexed

| Category | Source | Examples |
|----------|--------|----------|
| Common tactics | Built-in list | `norm_num`, `omega`, `ring`, `linarith` |
| Analysis | `Mathlib/Analysis/SpecialFunctions` | `sin_le_one`, `exp_pos`, `sqrt_nonneg` |
| Order theory | `Mathlib/Order` | `IsLeast`, `sSup`, bounds lemmas |
| Sets | `Mathlib/Data/Set` | `mem_Icc`, interval membership |
| Real numbers | `Mathlib/Data/Real` | Real-specific lemmas |

## Notes

- First run takes longer as it parses Mathlib sources
- Duplicate entries are skipped (safe to re-run)
- Spawns Lean processes to extract accurate type signatures
- Index is persistent in Ensue - only need to run once per Mathlib version
