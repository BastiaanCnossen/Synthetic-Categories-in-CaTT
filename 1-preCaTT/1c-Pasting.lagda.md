# 1c-Pasting: Dimensions and Pasting Contexts

This module equips the raw preCaTT syntax with:
- a dimension function on types, terms, and contexts
- the inductive notion of a **pasting context**
- the companion notion of a **dangling variable** inside a pasting context

A pasting context represents a composable cell-shape. It is built inductively
from `(x : ⋆)` by repeatedly choosing a dangling variable `x : A` and extending
the context by:
- a new target variable `y : A`
- a new arrow/cell `f : [ A ] x ⇒ y`

The crucial persistence rule is that previously dangling variables of strictly
lower dimension remain dangling after extension. This is encoded by the
`varps-weak` constructor.

```agda
module 1c-Pasting where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _⊔_; s≤s; z≤n)
open import Data.Nat.Properties
  using
    ( ≤-refl
    ; ≤-trans
    ; m≤m⊔n
    ; m≤n⊔m
    ; m≤n⇒m⊔n≡n
    ; m≥n⇒m⊔n≡m
    ; ⊔-lub
    ; n≤1+n
    )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import 1a-preCaTT
```

## Dimensions

```agda
-- Dimension of a type
dim-ty : ∀ {Γ} → Ty Γ → ℕ
dim-ty ⋆ = zero
dim-ty ([ A ] t ⇒ u) = suc (dim-ty A)

-- Dimension of a term
dim-tm : ∀ {Γ} → Tm Γ → ℕ
dim-tm t = dim-ty (tyOf t)

-- Dimension of a well-typed context
dim-ctx : Ctx → ℕ
dim-ctx ∅ = zero
dim-ctx (Γ , A) = dim-ctx Γ ⊔ dim-ty A

-- Weakening does not change dimension.
dim-ty-wkTy : ∀ {Γ} {A : Ty Γ} (B : Ty Γ) → dim-ty (wkTy {A = A} B) ≡ dim-ty B
dim-ty-wkTy ⋆ = refl
dim-ty-wkTy ([ B ] t ⇒ u) = cong suc (dim-ty-wkTy B)

-- Substitution preserves type dimension.
dim-ty-sub : ∀ {Γ Δ} (A : Ty Γ) (σ : Sub Δ Γ) → dim-ty (A [ σ ]T) ≡ dim-ty A
dim-ty-sub ⋆ σ = refl
dim-ty-sub ([ A ] t ⇒ u) σ = cong suc (dim-ty-sub A σ)

-- Every natural number is strictly smaller than its successor.
lt-self-suc : (n : ℕ) → n < suc n
lt-self-suc zero = s≤s z≤n
lt-self-suc (suc n) = s≤s (lt-self-suc n)

dim-var : ∀ {Γ} → Var Γ → ℕ
-- Variable dimension is just the dimension of its declared type.
dim-var x = dim-ty (var-to-type x)

dim-var-vs :
  ∀ {Γ} {A : Ty Γ}
  → (x : Var Γ)
  → dim-var {Γ = Γ , A} (vs x) ≡ dim-var x
dim-var-vs x = dim-ty-wkTy (var-to-type x)

dim-var-vz :
  ∀ {Γ} {A : Ty Γ}
  → dim-var {Γ = Γ , A} vz ≡ dim-var (vz {Γ} {A})
dim-var-vz {Γ} {A} = refl

dim-var≤dim-ctx : ∀ {Γ} (x : Var Γ) → dim-var x ≤ dim-ctx Γ
dim-var≤dim-ctx {Γ = Γ , A} vz rewrite dim-ty-wkTy {A = A} A =
  m≤n⊔m (dim-ctx Γ) (dim-ty A)
dim-var≤dim-ctx {Γ = Γ , A} (vs x) rewrite dim-var-vs {A = A} x =
  ≤-trans (dim-var≤dim-ctx x) (m≤m⊔n (dim-ctx Γ) (dim-ty A))
```

## Pasting Contexts

```agda
mutual
  -- `CtxPs Γ` means "Γ is a pasting context".
  data CtxPs : Ctx → Set
  -- `VarPs Γ Γps` means "a chosen dangling variable in the pasting context Γps".
  data VarPs : (Γ : Ctx) → CtxPs Γ → Set

  varps-to-var : ∀ {Γ} {Γps : CtxPs Γ} → VarPs Γ Γps → Var Γ

  varps-to-type : ∀ {Γ} {Γps : CtxPs Γ} → VarPs Γ Γps → Ty Γ
  -- A dangling variable determines its ambient type.
  varps-to-type xps = var-to-type (varps-to-var xps)

  varps-to-tm : ∀ {Γ} {Γps : CtxPs Γ} → VarPs Γ Γps → Tm Γ
  -- And therefore also a term in the same context.
  varps-to-tm xps = var (varps-to-var xps)

  hom-type-ext-p-src : ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → tyOf (var (vs {A = varps-to-type xps} (varps-to-var xps))) ≡ wkTy (varps-to-type xps)
  hom-type-ext-p-src xps = refl

  hom-type-ext-p-tgt : ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → tyOf (var (vz {A = varps-to-type xps})) ≡ wkTy (varps-to-type xps)
  hom-type-ext-p-tgt xps = refl

  hom-type-ext : ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps) → Ty (Γ , varps-to-type xps)
  hom-type-ext xps =
    [ wkTy (varps-to-type xps) ] var (vs (varps-to-var xps)) ⇒ var vz

  ext-ctx : ∀ {Γ} {Γps : CtxPs Γ} → VarPs Γ Γps → Ctx
  -- Extend by a new target variable `y : A` and a new cell `f : x ⇒ y`.
  ext-ctx {Γ} xps =
    (Γ , varps-to-type xps) , hom-type-ext xps

  varps-to-ctxps : ∀ {Γ} {Γps : CtxPs Γ} → VarPs Γ Γps → CtxPs Γ
  varps-to-ctxps {_} {Γps} _ = Γps

  data CtxPs where
    -- Base pasting context: a single object.
    ps-ob  : CtxPs (∅ , ⋆)
    -- Extend a pasting context along a chosen dangling variable.
    ps-ext : ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps) → CtxPs (ext-ctx xps)

  data VarPs where
    -- In `(x : ⋆)`, the unique dangling variable is `x`.
    varps-ob : VarPs (∅ , ⋆) ps-ob
    -- In an extension, the new cell `f` is dangling.
    varps-f  : ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps) → VarPs (ext-ctx xps) (ps-ext xps)
    -- The new target `y` is also dangling.
    varps-y  : ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps) → VarPs (ext-ctx xps) (ps-ext xps)
    -- Older dangling variables persist if their dimension is strictly smaller.
    varps-weak : ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps) (zps : VarPs Γ Γps)
               → dim-ty (varps-to-type zps) < dim-ty (varps-to-type xps)
               → VarPs (ext-ctx xps) (ps-ext xps)

  -- In `(x : ⋆)`, the dangling variable is the top variable.
  varps-to-var varps-ob = vz
  -- In an extension, `f` is the newest variable.
  varps-to-var (varps-f xps) = vz
  -- The new target `y` sits one step below `f`.
  varps-to-var (varps-y xps) = vs vz
  -- A persisted old dangling variable is weakened twice (across `y` and `f`).
  varps-to-var (varps-weak xps zps _) = vs (vs (varps-to-var zps))
```

## Pasting Dimension Helpers

```agda
-- Every dangling variable lives within the ambient context dimension.
dim-varps≤dim-ctx :
  ∀ {Γ} {Γps : CtxPs Γ}
  → (xps : VarPs Γ Γps)
  → dim-ty (varps-to-type xps) ≤ dim-ctx Γ
dim-varps≤dim-ctx xps = dim-var≤dim-ctx (varps-to-var xps)

-- Extending along a dangling variable can raise context dimension by at most one.
dim-ctx-ext≤suc :
  ∀ {Γ} {Γps : CtxPs Γ}
  → (xps : VarPs Γ Γps)
  → dim-ctx (ext-ctx xps) ≤ suc (dim-ctx Γ)
dim-ctx-ext≤suc {Γ} {Γps} xps with dim-varps≤dim-ctx xps
... | d≤Γ
  rewrite m≥n⇒m⊔n≡m d≤Γ
        | dim-ty-wkTy {A = varps-to-type xps} (varps-to-type xps) =
  ⊔-lub (n≤1+n (dim-ctx Γ)) (s≤s d≤Γ)

-- If the new cell dimension already fits inside Γ, the extension does not increase dimension at all.
dim-ctx-ext≤ctx-if-sucd≤ :
  ∀ {Γ} {Γps : CtxPs Γ}
  → (xps : VarPs Γ Γps)
  → suc (dim-ty (varps-to-type xps)) ≤ dim-ctx Γ
  → dim-ctx (ext-ctx xps) ≤ dim-ctx Γ
dim-ctx-ext≤ctx-if-sucd≤ {Γ} {Γps} xps sucd≤Γ with dim-varps≤dim-ctx xps
... | d≤Γ
  rewrite m≥n⇒m⊔n≡m d≤Γ
        | dim-ty-wkTy {A = varps-to-type xps} (varps-to-type xps) =
  ⊔-lub ≤-refl sucd≤Γ

-- The new target `y` has the same dimension as the old dangling variable it copies.
dim-varps-y :
  ∀ {Γ} {Γps : CtxPs Γ} (d : VarPs Γ Γps)
  → dim-ty (varps-to-type (varps-y d)) ≡ dim-ty (varps-to-type d)
dim-varps-y d =
  trans (dim-ty-wkTy (wkTy (varps-to-type d)))
    (dim-ty-wkTy (varps-to-type d))

-- Weakening an older dangling witness preserves its original dimension.
dim-varps-weak :
  ∀ {Γ} {Γps : CtxPs Γ}
  (xps zps : VarPs Γ Γps)
  (lt : dim-ty (varps-to-type zps) < dim-ty (varps-to-type xps))
  → dim-ty (varps-to-type (varps-weak xps zps lt))
    ≡ dim-ty (varps-to-type zps)
dim-varps-weak xps zps lt =
  trans (dim-ty-wkTy (wkTy (varps-to-type zps)))
    (dim-ty-wkTy (varps-to-type zps))

-- The new cell `f` sits exactly one dimension above its source/target type.
dim-varps-f :
  ∀ {Γ} {Γps : CtxPs Γ} (d : VarPs Γ Γps)
  → dim-ty (varps-to-type (varps-f d)) ≡ suc (dim-ty (varps-to-type d))
dim-varps-f d =
  trans (dim-ty-wkTy (hom-type-ext d))
    (cong suc (dim-ty-wkTy (varps-to-type d)))

-- In every extension, the target witness lies strictly below the new cell witness.
lt-varps-y-varps-f :
  ∀ {Γ} {Γps : CtxPs Γ} (d : VarPs Γ Γps)
  → dim-ty (varps-to-type (varps-y d)) < dim-ty (varps-to-type (varps-f d))
lt-varps-y-varps-f d rewrite dim-varps-y d =
  lt-self-suc (dim-ty (varps-to-type d))

-- The same strict inequality for the original dangling variable itself.
lt-varps-to-f :
  ∀ {Γ} {Γps : CtxPs Γ} (d : VarPs Γ Γps)
  → dim-ty (varps-to-type d) < dim-ty (varps-to-type (varps-f d))
lt-varps-to-f d rewrite dim-varps-f d = lt-self-suc (dim-ty (varps-to-type d))
```

## Test Cases

```agda
-- Test 1: (x : ⋆) is a pasting context
test-ob : CtxPs (∅ , ⋆)
test-ob = ps-ob

-- Test 2: (x : ⋆, y : ⋆, f : x ⇒ y) is a pasting context
test-arrow : CtxPs _
test-arrow = ps-ext varps-ob

-- Test 3: Composable arrows (x : ⋆, y : ⋆, f : x ⇒ y, z : ⋆, g : y ⇒ z)
test-comp : CtxPs _
test-comp = ps-ext (varps-y varps-ob)

-- Test 4: In test-comp, the variable g is dangling
test-comp-g : VarPs _ test-comp
test-comp-g = varps-f (varps-y varps-ob)

-- Test 5: In test-comp, the variable z is also dangling
test-comp-z : VarPs _ test-comp
test-comp-z = varps-y (varps-y varps-ob)

-- Test 6: 2-cell context (x, y, f, g, α)
test-2cell : CtxPs _
test-2cell = ps-ext (varps-f varps-ob)

-- Test 7: In test-2cell, y is still dangling via varps-weak
test-2cell-y : VarPs _ test-2cell
test-2cell-y = varps-weak (varps-f varps-ob) (varps-y varps-ob) (s≤s z≤n)

-- Test 8: 3-cell context (x, y, f, g, α, h, β)
test-3cell : CtxPs _
test-3cell = ps-ext (varps-f (varps-f varps-ob))

-- Test 9: In test-3cell, y is still dangling (dim 0 < dim 2)
test-3cell-y : VarPs _ test-3cell
test-3cell-y = varps-weak (varps-f (varps-f varps-ob))
                          (varps-weak (varps-f varps-ob) (varps-y varps-ob) (s≤s z≤n))
                          (s≤s z≤n)

-- Test 10: In test-3cell, h is also dangling (dim 1 < dim 2)
test-3cell-h : VarPs _ test-3cell
test-3cell-h = varps-weak (varps-f (varps-f varps-ob))
                          (varps-y (varps-f varps-ob))
                          (s≤s (s≤s z≤n))
```
