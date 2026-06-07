# 2b-Wrappers: Shared Typed Wrappers Used After `2a`

This file is now a small shared helper layer rather than a general facade over
all raw preCaTT operations.

Its current purpose is limited to the pieces that later `2-CaTT` files still use
in common:

- typed-indexed pasting-context aliases
- a typed wrapper for fullness
- typed wrappers for dependency predicates
- the two substitution-agreement lemmas used by `2e`

Everything else should either live directly in `2a-CaTT` or be imported from
the raw files at the point of use.

```agda
module 2b-Wrappers where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong)
open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Nat using (ℕ)

open import 2a-CaTT public
import 1a-preCaTT as Pre
import 1b-Dep as PreDep
import 1c-Pasting as PrePs
import 1d-Fullness as PreFull
```

## Pasting Context Wrappers

```agda
CtxPs : Ctx → Set
CtxPs Γ = PrePs.CtxPs (Raw-Ctx Γ)

VarPs : (Γ : Ctx) → CtxPs Γ → Set
VarPs Γ Γps = PrePs.VarPs (Raw-Ctx Γ) Γps

varps-to-type : ∀ {Γ} {Γps : CtxPs Γ} → VarPs Γ Γps → Ty Γ
varps-to-type {Γ} xps =
  var-to-type {Γ} (PrePs.varps-to-var {Γ = Raw-Ctx Γ} xps)
```

## Dimension Wrappers

```agda
dim-ty : ∀ {Γ} → Ty Γ → ℕ
dim-ty A = PrePs.dim-ty (Raw-Ty A)

dim-tm : ∀ {Γ} → Tm Γ → ℕ
dim-tm t = PrePs.dim-tm (Raw-Tm t)

dim-ctx : Ctx → ℕ
dim-ctx Γ = PrePs.dim-ctx (Raw-Ctx Γ)

dim-var : ∀ {Γ} → Var Γ → ℕ
dim-var x = PrePs.dim-var x
```

## Fullness Wrappers

```agda
in-src-bdry : ∀ {Γ} → CtxPs Γ → Var Γ → Bool
in-src-bdry Γps x = PreFull.in-src-bdry Γps x

in-tgt-bdry : ∀ {Γ} → CtxPs Γ → Var Γ → Bool
in-tgt-bdry Γps x = PreFull.in-tgt-bdry Γps x

check-COMP : ∀ {Γ} → CtxPs Γ → Tm Γ → Tm Γ → Bool
check-COMP Γps u v = PreFull.check-COMP Γps (Raw-Tm u) (Raw-Tm v)

check-INV : ∀ {Γ} → CtxPs Γ → Tm Γ → Tm Γ → Bool
check-INV Γps u v = PreFull.check-INV Γps (Raw-Tm u) (Raw-Tm v)

is-full : ∀ {Γ} → CtxPs Γ → Tm Γ → Tm Γ → Bool
is-full Γps u v = check-COMP Γps u v ∨ check-INV Γps u v
```

## Dependency Wrappers

```agda
depends-on-var-ty : ∀ {Γ} → Var Γ → Ty Γ → Bool
depends-on-var-ty x A = PreDep.depends-on-var-ty x (Raw-Ty A)

depends-on-var-tm : ∀ {Γ} → Var Γ → Tm Γ → Bool
-- Dependency is semantic and routed through the preCaTT dependency engine.
depends-on-var-tm x t = PreDep.depends-on-var-tm x (Raw-Tm t)

depends-on-var-sub-at : ∀ {Γ Δ} → Var Γ → Sub Γ Δ → Var Δ → Bool
depends-on-var-sub-at x σ y = PreDep.depends-on-var-sub-at x (Raw-Sub σ) y

depends-on-var-sub : ∀ {Γ Δ} → Var Γ → Sub Γ Δ → Bool
depends-on-var-sub x σ = PreDep.depends-on-var-sub x (Raw-Sub σ)

depends-on-var-sub-at-lookup :
  ∀ {Γ Δ} → (x : Var Γ) → (σ : Sub Γ Δ) → (y : Var Δ)
  → depends-on-var-sub-at x σ y ≡ depends-on-var-tm x (lookup y σ)
depends-on-var-sub-at-lookup x σ y =
  trans
    (PreDep.depends-on-var-sub-at-lookup x (Raw-Sub σ) y)
    refl

-- If a variable appears in the type of a term, then it also appears in the term.
dep-tyOf→dep-tm :
  ∀ {Γ}
  → (x : Var Γ) → (t : Tm Γ)
  → depends-on-var-ty {Γ = Γ} x (tyOf {Γ = Γ} t) ≡ true
  → depends-on-var-tm {Γ = Γ} x t ≡ true
dep-tyOf→dep-tm {Γ} x t h = PreDep.dep-tyOf→dep-tm {Γ = Raw-Ctx Γ} x (Raw-Tm t) h

-- Predicate-indexed dependency wrappers
depends-on-X-ty : ∀ {Γ} → (Var Γ → Bool) → Ty Γ → Bool
depends-on-X-ty {Γ} X A = PreDep.depends-on-X-ty X (Raw-Ty A)

depends-on-X-tm : ∀ {Γ} → (Var Γ → Bool) → Tm Γ → Bool
depends-on-X-tm {Γ} X t = PreDep.depends-on-X-tm X (Raw-Tm t)
```

## Dependency Consequences

```agda
-- If A is independent of X, every variable used by A lies outside X.
indep-outside : ∀ {Γ} → (X : Var Γ → Bool) → (A : Ty Γ)
  → depends-on-X-ty {Γ = Γ} X A ≡ false
  → (x : Var Γ) → depends-on-var-ty {Γ = Γ} x A ≡ true → X x ≡ false
indep-outside X A = PreDep.indep-outside X (Raw-Ty A)

-- Term analogue of indep-outside.
indep-outside-tm : ∀ {Γ} → (X : Var Γ → Bool) → (t : Tm Γ)
  → depends-on-X-tm {Γ = Γ} X t ≡ false
  → (x : Var Γ) → depends-on-var-tm {Γ = Γ} x t ≡ true → X x ≡ false
indep-outside-tm X t = PreDep.indep-outside-tm X (Raw-Tm t)
```

## Agreement Lemmas

```agda
sub-agree-ty : ∀ {Γ Δ} (A : Ty Γ) (σ τ : Sub Δ Γ)
  → ((x : Var Γ)
    → depends-on-var-ty {Γ} x A ≡ true
    → _[_]t {Γ = Δ} {Δ = Γ} (var {Γ} x) σ
      ≡ _[_]t {Γ = Δ} {Δ = Γ} (var {Γ} x) τ)
  → _[_]T {Γ = Δ} {Δ = Γ} A σ
    ≡ _[_]T {Γ = Δ} {Δ = Γ} A τ
sub-agree-ty {Δ = Δ} (mkTy Pre.⋆ ⋆wf) σ τ P = refl
sub-agree-ty {Δ = Δ} A σ τ P =
  Ty-ext {Γ = Δ}
    (PreDep.sub-agree-ty (Raw-Ty A) (Raw-Sub σ) (Raw-Sub τ)
      (λ x dx → cong Raw-Tm (P x dx)))

sub-agree-tm : ∀ {Γ Δ} (t : Tm Γ) (σ τ : Sub Δ Γ)
  → ((x : Var Γ)
    → depends-on-var-tm {Γ} x t ≡ true
    → _[_]t {Γ = Δ} {Δ = Γ} (var {Γ} x) σ
      ≡ _[_]t {Γ = Δ} {Δ = Γ} (var {Γ} x) τ)
  → _[_]t {Γ = Δ} {Δ = Γ} t σ
    ≡ _[_]t {Γ = Δ} {Δ = Γ} t τ
sub-agree-tm {Δ = Δ} t σ τ P =
  Tm-ext {Γ = Δ}
    (PreDep.sub-agree-tm (Raw-Tm t) (Raw-Sub σ) (Raw-Sub τ)
      (λ x dx → cong Raw-Tm (P x dx)))
```
