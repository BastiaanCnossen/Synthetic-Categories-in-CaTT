# 4-Naturality — The Naturality Construction

This subbranch implements the **naturality construction** of Benjamin-Markakis-Offord-Sarti-Vicary (BMOSV), extended to arbitrary coherence depth. The naturality construction transforms terms into "naturality witnesses" showing how they vary as their parameters change.

---

## Purpose

Given a context Γ and an **up-closed** set X of variables, the naturality construction produces:
- **Suspended contexts** `Γ ⋊ X` (semi-suspended) and `Γ ↑ X` (fully suspended)
- **Naturality types** `A ↑ X` with iterated whiskering when depth > 0
- **Naturality terms** `t ↑ X` witnessing how t varies from `t[in⁻]` to `t[in⁺]`
- **Naturality substitutions** `γ ↑ X`

Unlike functoriality (which handles only locally maximal dimension variables), naturality handles general up-closed sets. This introduces the complication that naturality types involve **iterated whiskering** when variables of different dimensions are suspended.

---

## Core Concepts

### Up-closed Sets

A set `X ⊆ Var(Γ)` is **up-closed** if whenever `x ∈ X` and `y` appears in the type of `x`, then `y ∈ X`.

**Example:** In context `(x, y : Ob, f : x → y)`:
- `{f}` is up-closed (nothing appears in f's type that isn't already in the context)
- `{x, f}` is up-closed
- `{f, y}` is **not** up-closed (missing x, which appears in f's type)

### Coherence Depth

The **coherence depth** `cdepth_X(t)` refines the simple depth by tracking the depths of coherences appearing in a term. The naturality construction requires `cdepth_X ≤ 1`.

### Suspended Contexts

For up-closed X:
- **Semi-suspended** `Γ ⋊ X`: contains `x⁻, x⁺` for each `x ∈ X`
- **Fully suspended** `Γ ↑ X`: also contains `x̃` for each `x ∈ X`

The naturality cell `x̃` has type `(A ↑ X')[x⁻/v⁻, x⁺/v⁺]` where A is the type of x and X' = X \ {x}.

### Source and Target Types

When depth > 0, the naturality type involves **iterated whiskering**:
```
A ↑ X := (s^A_X(v⁻) →_{S^A_X(A)} t^A_X(v⁺))
```

The source type `S^A_X(B)` and target type `T^A_X(B)` are parameterized by an auxiliary type B with `∂*(B) ≡ A`, allowing recursive tracking of whiskerings.

---

## Planned Modules

### 4a-UpClosed.lagda.md
- Definition of up-closed sets
- Checking up-closure
- Operations: union, intersection, complement w.r.t. Var(Γ)

### 4b-CoherenceDepth.lagda.md
- Coherence depth for terms, types, substitutions
- Computing coherence depth
- Comparison with simple depth

### 4c-SuspendedCtx.lagda.md
- Semi-suspended context `Γ ⋊ X`
- Fully suspended context `Γ ↑ X`
- Inclusion substitutions `in⁻` and `in⁺`

### 4d-SourceTarget.lagda.md
- Source types `S^A_X(B)` and source terms `s^A_X(b)`
- Target types `T^A_X(B)` and target terms `t^A_X(b)`
- Parameterization by auxiliary type B with `∂*(B) ≡ A`
- Uses higher whiskering from 3-Functoriality

### 4e-NatTypes.lagda.md
- Naturality of types: `A ↑ X`
- Construction using source/target types

### 4f-NatTerms.lagda.md
- Naturality of variables: `x ↑ X = x̃`
- Naturality of coherences: `(coh_{Γ,A}[γ]) ↑ X`

### 4g-NatSubs.lagda.md
- Naturality of substitutions: `γ ↑ X`
- Compatibility with context extension

---

## Dependencies

**Imports:**
- `2-CaTT-Basic` (contexts, types, terms, pasting, fullness)
- `3-Functoriality` (higher whiskering for source/target types)

**Used by:**
- `5-Diagrams` (hom-types between diagrams are constructed via naturality)

---

## Mathematical Reference

See:
- `MATH_REFERENCE.md` Sections 4-6 (Coherence depth, Up-closed sets, Naturality)
- `../Thoughts series/Thoughts18.tex` Section 4

---

## Agda Module (to be implemented)

```agda
module I-CaTT.4-Naturality.4-Naturality where

-- Re-export all submodules
open import I-CaTT.4-Naturality.4a-UpClosed public
open import I-CaTT.4-Naturality.4b-CoherenceDepth public
open import I-CaTT.4-Naturality.4c-SuspendedCtx public
open import I-CaTT.4-Naturality.4d-SourceTarget public
open import I-CaTT.4-Naturality.4e-NatTypes public
open import I-CaTT.4-Naturality.4f-NatTerms public
open import I-CaTT.4-Naturality.4g-NatSubs public
```
