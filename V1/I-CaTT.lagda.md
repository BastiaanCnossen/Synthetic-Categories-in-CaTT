# I-CaTT — Category Type Theory Infrastructure

This is the main branch for the foundational infrastructure of **Category Type Theory (CaTT)**. It provides all the machinery needed before we can define actual categorical structures like products, pullbacks, and internal homs.

---

## What is CaTT?

CaTT is a type theory for **weak ω-categories**, introduced by Finster and Mimram and developed further by Benjamin, Finster, and Mimram. Unlike traditional approaches where categories are defined as sets with structure, CaTT treats categorical structure as primitive in the type theory itself.

### The Basic Structure

In CaTT, types describe the "shape" of cells in a weak ω-category:

- **Objects (0-cells):** There is a base type `Ob` whose terms are objects.
- **Morphisms (1-cells):** For terms `x, y : Ob`, there is a hom-type `(x → y)` whose terms are morphisms from x to y.
- **2-cells:** For morphisms `f, g : x → y`, there is a type `(f → g)` whose terms are 2-cells.
- **n-cells:** This pattern continues to arbitrarily high dimensions.

The syntax `(t →_A u)` denotes a hom-type where the source t and target u have type A. When A = Ob, we often write simply `(t → u)`.

### Pasting Contexts and Coherences

Not every context in CaTT represents a meaningful configuration of cells. A **pasting context** is a special kind of context that represents a composable arrangement of cells—like a pasting diagram in higher category theory.

In a pasting context Γ, we can form **coherence terms** via the `coh` rule:

Γ ⊢ps                     Γ ⊢ u : A    Γ ⊢ v : A
─────────────────────────────────────────────────
     Γ ⊢ coh_{Γ,A}(u,v) : (u →_A v)

The coherence `coh_{Γ,A}(u,v)` witnesses that u and v are related in a canonical way determined by the pasting context Γ.

### Fullness Conditions

Not every coherence is allowed—we impose **fullness conditions** to ensure coherences are well-behaved:

- **(COMP)** — for composites: The source u must use exactly the variables of the source boundary ∂⁻Γ, and the target v must use exactly the variables of the target boundary ∂⁺Γ.

- **(INV)** — for invertible coherences: Both u and v must use all variables of Γ.

These conditions ensure that coherences genuinely represent composites (like `g ∘ f`) or coherence isomorphisms (like associators and unitors).

### Distinction from HoTT-based Approaches

Unlike HoTT-based synthetic category theory (such as Riehl-Shulman or Buchholtz-Weinberger), CaTT does not assume any strictness:

- **No judgmental associativity:** The associativity `(h ∘ g) ∘ f ≃ h ∘ (g ∘ f)` is not a definitional equality; it's witnessed by an explicit coherence term.
- **No judgmental unitality:** Similarly, `id ∘ f ≃ f` and `f ∘ id ≃ f` are coherences, not equalities.
- **All coherences derived:** Every coherence (associators, unitors, interchangers, etc.) arises as an instance of the `coh` rule applied to an appropriate pasting context.

This makes CaTT a natural setting for working with fully weak higher categorical structures.

---

## Structure of This Branch

The I-CaTT branch is divided into four subbranches, each building on the previous:

### 1-GSeTT-Basic: Raw Pre-Syntax Layer

Sets up the raw type-theoretic infrastructure (GSeTT):

| Module | Purpose |
|--------|---------|
| 1a-GSeTT | Contexts, types, substitutions, and terms with rewriting |
| 1b-Norm | Normalization and extensionality |
| 1c-Dep | Dependency analysis |
| 1d-Dim | Dimensions of types, iterated desuspension (`∂*(B) ≡ A`) |
| 1e-Pasting | Pasting contexts with dangling variables |
| 1f-Boundaries | Source/target i-dimensional boundary functions (∂⁻ᵢΓ, ∂⁺ᵢΓ) |
| 1g-Fullness | Fullness conditions (COMP) and (INV) for coherences |

**Status:** Complete.

### 2-CaTT-Basic: Core CaTT Type Theory

Builds the fullness-enforced CaTT layer on top of GSeTT:

| Module | Purpose |
|--------|---------|
| 2a-CaTT | Core CaTT with `coh` constructor and `toRaw-*` conversions |
| 2b-Norm | CaTT normalization and extensionality |
| 2c-Examples | Basic coherences (identity, composition, associator, etc.) |
| 2d-Dep | CaTT dependency analysis |
| 2e-Wrappers | CaTT-facing wrappers for dim/pasting/boundary/fullness |
| 2f-Lemmas | Dimension/dependency lemmas for functoriality |

**Status:** Complete.

### 3-Functoriality: The Functoriality Construction

Implements functoriality for variables of **locally maximal dimension**:

- **Functoriality of contexts:** Given Γ and a set X of locally maximal dimension variables, construct `Γ ↑ X` with split variables `x⁻`, `x⁺`, and naturality cells `x̃`.
- **Functoriality of terms:** When `depth_X(t) = 0`, construct `t ↑ X`.
- **Disk and composition contexts:** Build the standard contexts for n-cells and their compositions.
- **Higher whiskering:** Define `g ⋆ α` (whiskering α by g) at all dimensions.

Functoriality is a special case of naturality that must be developed first, as it is used in the naturality construction itself.

**Status:** In progress. See `3-Functoriality/3-Functoriality.lagda.md`.

### 4-Naturality: The Naturality Construction

Implements the full naturality construction of Benjamin-Markakis-Offord-Sarti-Vicary, extended to arbitrary coherence depth:

- **Up-closed sets:** A set X ⊆ Var(Γ) where if x ∈ X and y appears in the type of x, then y ∈ X.
- **Suspended contexts:** Semi-suspended `Γ ⋊ X` and fully suspended `Γ ↑ X`.
- **Source/target types:** `S^A_X(B)` and `T^A_X(B)` with iterated whiskering when depth > 0.
- **Naturality types:** `A ↑ X := (s^A_X(v⁻) →_{S^A_X(A)} t^A_X(v⁺))`
- **Naturality terms:** `t ↑ X` witnessing how t varies from `t[in⁻]` to `t[in⁺]`.

The key innovation is bounding **coherence depth** rather than simple depth, which allows the construction to proceed by induction.

**Status:** Stub only. See `4-Naturality/4-Naturality.lagda.md` for the planned structure.

### 5-Diagrams: Diagram Types and Universal Properties

Introduces the formalism for expressing universal properties:

- **Diagram types:** Finite lists `A = (A₁, ..., Aₙ)` treated as single types.
- **Hom-types between diagrams:** `(a →_A b)` constructed via naturality.
- **Morphisms:** `φ : A ⇝ B` as diagrams of B parametrized by diagrams of A.
- **Equivalences:** Morphisms with inverses up to lax transformation.
- **Cone types:** Diagram types `A(t)` depending on a cone point, with contravariant functoriality.
- **Universality:** When the Yoneda map `Y_τ : (t → x) ⇝ A(t)` is an equivalence.

This is the bridge to branch II-Categories, where products, pullbacks, and internal homs are defined using these concepts.

**Status:** Stub only. See `5-Diagrams/5-Diagrams.lagda.md` for the planned structure.

---

## Dependency Flow

The subbranches form a linear dependency chain:

```
1-GSeTT-Basic
     │
     │ provides: raw pre-syntax, normalization, dependency, pasting, fullness
     ▼
2-CaTT-Basic
     │
     │ provides: CaTT with fullness, CaTT dependency, wrappers, lemmas
     ▼
3-Functoriality
     │
     │ provides: higher whiskering, disk/composition contexts
     ▼
4-Naturality
     │
     │ provides: naturality types and terms, suspended contexts
     ▼
5-Diagrams
     │
     │ provides: diagram types, hom-types, cone types, universality
     ▼
[II-Categories branch]
```

---

## Mathematical References

For the mathematics underlying this branch:

- **Pasting contexts and fullness:** `MATH_REFERENCE.md` Sections 1-2
- **Functoriality:** `MATH_REFERENCE.md` Section 3, `Thoughts18.tex` Section 3
- **Naturality:** `MATH_REFERENCE.md` Sections 4-6, `Thoughts18.tex` Section 4
- **Diagram types:** `MATH_REFERENCE.md` Section 8, `Thoughts18.tex` Sections 5-6

---

## Agda Module (to be implemented)

When complete, this module will re-export all definitions from the I-CaTT branch:

```agda
module I-CaTT.I-CaTT where

-- Core CaTT infrastructure
open import I-CaTT.1-preCaTT.1-preCaTT public

-- CaTT type theory
open import I-CaTT.2-CaTT.2-CaTT public

-- Functoriality construction
open import I-CaTT.3-Functoriality.3-Functoriality public

-- Naturality construction
open import I-CaTT.4-Naturality.4-Naturality public

-- Diagram types and universal properties
open import I-CaTT.5-Diagrams.5-Diagrams public
```
