# 2f-Depth: Depth for the Depth-0 Functoriality Fragment

This module defines numeric depth for types, terms, and substitutions relative
to a selected variable predicate `X`.

For a term `t : A`, a type `A`, or a substitution `γ : Γ`, and a set
`X ⊆ Var(Γ)`, the intended formulas are:

```text
depth_X(t) := max { dim(t) - dim(x) : x ∈ Var(t : A) ∩ X }
depth_X(A) := max { dim(A) - dim(x) : x ∈ Var(A) ∩ X }
depth_X(γ) := max { depth_X(y[γ]) : y ∈ Var(Γ) }
```

By convention, `max ∅ = -1`. So if `X` does not meet the variables actually
used by `t` or `A`, the corresponding depth is `-1`.

The coding convention is:

- `none` represents the empty-maximum case, i.e. semantic depth `-1`
- `some n` represents semantic depth `n`

So `depth≤0` is true exactly for the cases `-1` and `0`, which is the fragment
used by the basic functoriality construction before composition and whiskering.

The archived V7 development also used a separate dimension/dependency lemma
layer before the depth corollaries. The wrapper surface needed for that layer
has been restored in `2b-Wrappers`; the two consequences currently used by `2f`
remain postulated below until those proofs are ported.

```agda
module 2f-Depth where

open import Agda.Builtin.Equality
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _∸_)

import 1a-preCaTT as Pre
open import 2b-Wrappers hiding (zero)
```

## Basic Setup

```agda
data Depth : Set where
  none : Depth
  some : ℕ → Depth

depth-max : Depth → Depth → Depth
depth-max none d = d
depth-max d none = d
depth-max (some m) (some n) = some (m ⊔ n)

pick-depth : Bool → ℕ → Depth
pick-depth false n = none
pick-depth true n = some n

max-over-vars : {Γ : Ctx} → (Var Γ → Depth) → Depth
max-over-vars {Γ = mkCtx Pre.∅ ∅wf} f = none
max-over-vars {Γ = mkCtx _ (_,_wf {Γ = Γraw} Γwf A0)} f =
  depth-max (f Pre.vz) (max-over-vars {Γ = mkCtx Γraw Γwf} (λ x → f (Pre.vs x)))
```

## Definition of Depth

```agda
-- The depth of a type is the largest dimension drop from the type to an
-- actually used selected variable.
depth-ty : {Γ : Ctx} → (X : Var Γ → Bool) → Ty Γ → Depth
depth-ty {Γ} X A =
  max-over-vars {Γ = Γ}
    (λ x → pick-depth (X x ∧ depends-on-var-ty {Γ = Γ} x A) (dim-ty A ∸ dim-var {Γ = Γ} x))

-- The depth of a term is the largest dimension drop from the term to an
-- actually used selected variable.
depth-tm : {Γ : Ctx} → (X : Var Γ → Bool) → Tm Γ → Depth
depth-tm {Γ} X t =
  max-over-vars {Γ = Γ}
    (λ x → pick-depth (X x ∧ depends-on-var-tm {Γ = Γ} x t) (dim-tm t ∸ dim-var {Γ = Γ} x))

-- The depth of a substitution is the maximum depth of the images y[σ] of target
-- variables y.
depth-sub : {Γ Δ : Ctx} → (X : Var Γ → Bool) → Sub Γ Δ → Depth
depth-sub {Γ} {Δ} X σ =
  max-over-vars {Γ = Δ} (λ y → depth-tm {Γ} X (var y [ σ ]t))
```

## Bounded Depth

```agda
depth≤0 : Depth → Bool
depth≤0 none = true
depth≤0 (some zero) = true
depth≤0 (some (suc n)) = false

depth≤0-ty : {Γ : Ctx} → (X : Var Γ → Bool) → Ty Γ → Bool
depth≤0-ty X A = depth≤0 (depth-ty X A)

depth≤0-tm : {Γ : Ctx} → (X : Var Γ → Bool) → Tm Γ → Bool
depth≤0-tm X t = depth≤0 (depth-tm X t)

depth≤0-sub : {Γ Δ : Ctx} → (X : Var Γ → Bool) → Sub Γ Δ → Bool
depth≤0-sub X σ = depth≤0 (depth-sub X σ)

depth=0 : Depth → Bool
depth=0 none = false
depth=0 (some zero) = true
depth=0 (some _) = false

depth=0-tm : {Γ : Ctx} → (X : Var Γ → Bool) → Tm Γ → Bool
depth=0-tm X t = depth=0 (depth-tm X t)

depth=0-sub : {Γ Δ : Ctx} → (X : Var Γ → Bool) → Sub Γ Δ → Bool
depth=0-sub X σ = depth=0 (depth-sub X σ)
```

## Deferred Corollaries

```agda
-- If `depth-max d e` has depth at most 0, then so does each component.
depth≤0-depth-max-left : {d e : Depth} → depth≤0 (depth-max d e) ≡ true → depth≤0 d ≡ true
depth≤0-depth-max-left {none} p = refl
depth≤0-depth-max-left {some zero} {none} p = refl
depth≤0-depth-max-left {some zero} {some zero} p = refl
depth≤0-depth-max-left {some zero} {some (suc n)} ()
depth≤0-depth-max-left {some (suc m)} {none} ()
depth≤0-depth-max-left {some (suc m)} {some zero} ()
depth≤0-depth-max-left {some (suc m)} {some (suc n)} ()

depth≤0-depth-max-right : {d e : Depth} → depth≤0 (depth-max d e) ≡ true → depth≤0 e ≡ true
depth≤0-depth-max-right {none} p = p
depth≤0-depth-max-right {some n} {none} p = refl
depth≤0-depth-max-right {some zero} {some zero} p = refl
depth≤0-depth-max-right {some zero} {some (suc n)} ()
depth≤0-depth-max-right {some (suc m)} {some zero} ()
depth≤0-depth-max-right {some (suc m)} {some (suc n)} ()

postulate
  depth≤0-ty→depends-on-X-ty-false :
    {Γ : Ctx}
    → (X : Var Γ → Bool)
    → (A : Ty Γ)
    → depth≤0-ty {Γ = Γ} X A ≡ true
    → depends-on-X-ty {Γ = Γ} X A ≡ false

depth≤0-sub-tail-local :
  {Γ Δ : Ctx}
  {A : Ty Δ}
  {γ : Sub Γ Δ}
  {t : Tm Γ}
  {p : TmTyEqSub {Γ = Γ} {Δ = Δ} t A γ}
  → (X : Var Γ → Bool)
  → depth≤0-sub {Γ = Γ} {Δ = Δ , A} X (⟨ γ , t ⟩∶[ p ]) ≡ true
  → depth≤0-sub {Γ = Γ} {Δ = Δ} X γ ≡ true
depth≤0-sub-tail-local {γ = γ} {t = t} X d =
  depth≤0-depth-max-right
    {d = depth-tm X t}
    {e = depth-sub X γ}
    d
```
