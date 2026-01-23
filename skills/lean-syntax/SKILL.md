# Lean 4 Syntax Guide for Goal Generation

**Use this skill when creating goals with `./bin/lc create-goal`.**

This ensures your `--goal-type` and `--hypotheses` are syntactically valid Lean 4.

---

## Function Application (NO PARENTHESES)

Lean 4 uses juxtaposition, not parentheses:

| WRONG | CORRECT |
|-------|---------|
| `sin(x)` | `Real.sin x` |
| `cos(y)` | `Real.cos y` |
| `exp(x)` | `Real.exp x` |
| `log(x)` | `Real.log x` |
| `sqrt(x)` | `Real.sqrt x` |
| `abs(x)` | `|x|` or `abs x` |
| `f(x, y)` | `f x y` |

**Multi-argument functions:**
```lean
-- WRONG
max(a, b)
min(x, y)

-- CORRECT
max a b
min x y
```

---

## Real Number Constants

| WRONG | CORRECT |
|-------|---------|
| `π` | `Real.pi` |
| `e` | `Real.exp 1` |
| `0.5` | `1/2` (prefer rationals) |
| `pi/2` | `Real.pi / 2` |

---

## Set Notation

### Intervals

| Interval | Lean 4 Syntax |
|----------|---------------|
| `[a, b]` | `Set.Icc a b` |
| `(a, b)` | `Set.Ioo a b` |
| `[a, b)` | `Set.Ico a b` |
| `(a, b]` | `Set.Ioc a b` |

**Examples:**
```lean
-- WRONG
x ∈ [0, π/2]
x ∈ (0, 1)

-- CORRECT
x ∈ Set.Icc 0 (Real.pi / 2)
x ∈ Set.Ioo 0 1
```

### Set Membership

```lean
-- WRONG
x ∈ {y | P(y)}

-- CORRECT (simple predicate)
x ∈ {y | P y}

-- BETTER (avoid set-builder in goal types - decompose instead)
-- Instead of: x ∈ {c | ∀ y ∈ S, f c y}
-- Create separate goals:
--   1. "∀ y ∈ S, f x y" (the membership condition)
--   2. The remaining proof
```

---

## Hypotheses Format

**Format:** Double-semicolon (`;;`) separated `name : type` pairs

```bash
--hypotheses "x : ℝ;;hx : x ∈ Set.Icc 0 Real.pi"
```

**Why `;;`?** Commas appear inside Lean types (like `∀ x ∈ S, P x`), so we use `;;` which never appears in valid Lean.

### Quantifiers Are Now Safe

With `;;` delimiter, quantified hypotheses work correctly:

```bash
# WORKS - ;; delimiter handles internal commas
--hypotheses "c : ℝ;;hc : ∀ x ∈ Set.Icc 0 (Real.pi / 2), Real.sin x ≤ c * x"

# This correctly becomes TWO hypotheses:
#   1. c : ℝ
#   2. hc : ∀ x ∈ Set.Icc 0 (Real.pi / 2), Real.sin x ≤ c * x
```

### Examples

| After decomposition | Hypotheses to pass |
|--------------------|-------------------|
| `intro x hx` | `--hypotheses "x : ℝ;;hx : x ∈ Set.Icc 0 Real.pi"` |
| `intro c hc` (membership) | `--hypotheses "c : ℝ;;hc : ∀ x ∈ S, P x"` |
| Multiple intros | `--hypotheses "a : ℝ;;ha : a > 0;;b : ℝ;;hb : b < 1"` |

### Parentheses Must Match

Count your parentheses! Common error:

```bash
-- WRONG (unmatched paren)
--hypotheses "h : (4 / Real.pi ^ 2) * (Real.pi - x) * x"
                                                      ^ missing close?

-- CORRECT
--hypotheses "h : (4 / Real.pi ^ 2) * (Real.pi - x) * x ≥ 0"
```

### Empty Hypotheses

```bash
-- WRONG (causes syntax error)
--hypotheses ""

-- CORRECT (omit entirely for root goals)
./bin/lc create-goal --id "my-goal" --goal-type "P" --parent "root" --depth 1
```

---

## Operators and Inequalities

| Symbol | Lean 4 |
|--------|--------|
| `≤` | `≤` (Unicode) or `<=` |
| `≥` | `≥` (Unicode) or `>=` |
| `<` | `<` |
| `>` | `>` |
| `≠` | `≠` (Unicode) or `!=` |
| `∧` | `∧` (Unicode) or `/\` |
| `∨` | `∨` (Unicode) or `\/` |
| `→` | `→` (Unicode) or `->` |
| `∀` | `∀` (Unicode) or `forall` |
| `∃` | `∃` (Unicode) or `exists` |

---

## Division and Powers

```lean
-- Division
4 / Real.pi         -- division
(4 : ℝ) / Real.pi   -- explicit type annotation if needed

-- Powers
Real.pi ^ 2         -- pi squared
x ^ (1/2)           -- square root (or use Real.sqrt x)
Real.exp x          -- e^x

-- WRONG
π²
pi**2

-- CORRECT
Real.pi ^ 2
```

---

## Common Goal Patterns

### IsGreatest / IsLeast

```lean
-- Goal type for IsGreatest
IsGreatest {c | ∀ x ∈ Set.Icc 0 (Real.pi / 2), c * x ≤ Real.sin x} (2 / Real.pi)

-- After `constructor`, children are:
-- 1. Membership: (2 / Real.pi) ∈ {c | ∀ x ∈ ..., c * x ≤ Real.sin x}
-- 2. Upper bound: ∀ c ∈ {c | ...}, c ≤ 2 / Real.pi
```

### Quantifier Introduction

```lean
-- Parent: ∀ x ∈ Set.Icc 0 (Real.pi / 2), P x
-- After `intro x hx`:
-- Child goal: P x
-- Child hypotheses: "x : ℝ,hx : x ∈ Set.Icc 0 (Real.pi / 2)"
```

### Conjunction

```lean
-- Parent: P ∧ Q
-- After `constructor`:
-- Child 1: P
-- Child 2: Q
-- (hypotheses inherited from parent)
```

---

## Validation Checklist

Before calling `./bin/lc create-goal`, verify:

1. **Parentheses match** - count `(` and `)`, must be equal
2. **No commas in types** - split quantified hypotheses
3. **Function application** - `Real.sin x` not `sin(x)`
4. **Intervals** - `Set.Icc a b` not `[a, b]`
5. **Constants** - `Real.pi` not `π`
6. **Spaces around operators** - `a ≤ b` not `a≤b`

---

## Quick Reference

```lean
-- Trigonometric
Real.sin x, Real.cos x, Real.tan x

-- Arithmetic
a + b, a - b, a * b, a / b, a ^ n

-- Comparisons
a ≤ b, a < b, a = b, a ≠ b

-- Logic
P ∧ Q, P ∨ Q, P → Q, ¬P

-- Quantifiers (in goal types)
∀ x, P x
∀ x ∈ S, P x
∃ x, P x

-- Sets
x ∈ S
Set.Icc a b  -- [a, b]
Set.Ioo a b  -- (a, b)

-- Special structures
IsGreatest S x
IsLeast S x
ConcaveOn ℝ S f
ConvexOn ℝ S f
```
