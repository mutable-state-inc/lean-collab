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

## 🚨 Commonly Hallucinated Lemmas → Correct Names

**LLMs frequently guess lemma names that don't exist.** Use `./bin/lc suggest` to get real ones, or consult this table.

### Set/Metric Theory

| WRONG (Hallucinated) | CORRECT (Mathlib) | Notes |
|---------------------|-------------------|-------|
| `Metric.Sphere.infinite` | `Metric.sphere_infinite` | Lowercase, underscore |
| `Set.Infinite.diff` | `Set.Infinite.diff` | Check signature - needs `Finite` second arg |
| `Set.infinite_sphere` | `Metric.sphere_infinite` | In Metric namespace |
| `Metric.sphere.nonempty` | `Metric.nonempty_sphere` | Prefix not suffix |
| `Set.Infinite.inter` | `Set.Infinite.inter_of_left` | Needs side specification |

### Geometry/Euclidean

| WRONG (Hallucinated) | CORRECT (Mathlib) | Notes |
|---------------------|-------------------|-------|
| `EuclideanGeometry.sphere_infinite` | `Metric.sphere_infinite` | It's in Metric |
| `Affine.Simplex.circumcenter` | `Affine.Simplex.circumcenter` | ✓ exists, check args |
| `circumcenter_mem_sphere` | `Affine.Simplex.circumsphere_center_eq_circumcenter` | Different name |
| `Simplex.monochromatic` | N/A | You need to define this |

### Trigonometry

| WRONG (Hallucinated) | CORRECT (Mathlib) | Notes |
|---------------------|-------------------|-------|
| `Real.sin_le_one` | `Real.sin_le_one` | ✓ exists |
| `Real.two_div_pi_mul_le_sin` | `Real.two_div_pi_mul_le_sin` | ✓ exists (Jordan) |
| `sin_pos_of_pos_of_lt_pi` | `Real.sin_pos_of_pos_of_lt_pi` | Need `Real.` prefix |
| `sin_nonneg_of_nonneg_of_le_pi` | `Real.sin_nonneg_of_nonneg_of_le_pi` | Need `Real.` prefix |
| `cos_pos_of_mem_Ioo` | `Real.cos_pos_of_mem_Ioo` | Need `Real.` prefix |

### Cardinality/Finiteness

| WRONG (Hallucinated) | CORRECT (Mathlib) | Notes |
|---------------------|-------------------|-------|
| `Finset.card_le_three` | N/A | Use `Finset.card_le_of_subset` |
| `Set.nontrivial_of_card_ge_two` | `Set.nontrivial_of_two_le_card` | Reversed name |
| `Finite.of_card_le` | `Set.Finite.of_card_le` | Need `Set.` prefix |

### Convexity/Concavity

| WRONG (Hallucinated) | CORRECT (Mathlib) | Notes |
|---------------------|-------------------|-------|
| `ConcaveOn.sin` | `strictConcaveOn_sin_Icc` | Different structure |
| `concave_sin_Icc` | `strictConcaveOn_sin_Icc.concaveOn` | Need `.concaveOn` |
| `ConvexOn.le_right` | `ConvexOn.le_right_of_lt_left` | Full name needed |

### General Patterns

**Naming conventions in Mathlib:**
- `snake_case` not `camelCase` for lemmas
- Prefix with namespace: `Real.sin_zero` not `sin_zero`
- Predicates often have `_of_` for implications: `sin_pos_of_pos`
- Interval versions often have `_Icc`, `_Ioo` suffix

**When you get "unknown identifier":**
```bash
# 1. ALWAYS try suggest first
./bin/lc suggest --goal $GOAL_ID

# 2. Search for similar patterns
./bin/lc search "sphere infinite" --prefix tactics/

# 3. Check the actual Mathlib namespace (in Lean REPL)
#check @Metric.sphere_infinite  -- see the real signature
```

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
