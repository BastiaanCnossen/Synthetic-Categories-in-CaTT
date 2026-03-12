# 1b-Dep: Variable Dependency

This module defines **semantic** dependency predicates (not mere syntactic
occurrence checks) for the raw preCaTT syntax.

For variables:
- A variable `y` semantically depends on `x` if either `x = y`, or `x`
  appears in the declared type of `y`.

For terms:
- A variable term `var y` depends on `x` exactly when `y` depends on `x`
  in the semantic variable sense above.
- A raw coherence `coh-raw A u v σ` depends on those variables that the
  stored substitution `σ` depends on.

For types:
- `⋆` has no variable dependencies.
- A hom-type `[ A ] t ⇒ u` depends on `x` when the base type `A`, source `t`,
  or target `u` depends on `x`.

For substitutions:
- `depends-on-var-sub-at x σ y` asks whether the image of the variable `y`
  under `σ` depends on `x`.
- `depends-on-var-sub x σ` asks whether there exists a variable `y` in the
  codomain context which has an image that depends on `x`.

```agda
module 1b-Dep where

open import 1a-preCaTT
  hiding (lookup-wkSub; lookup-idS; ∃-var-point-false; ∃-var-all-false)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; trans ; sym ; cong ; cong₂ ; subst)
open import Data.Bool.Base using (Bool; true; false; _∨_; _∧_)
open import 0a-Logic
```

## Core Recursive Engine (Pre-Syntax)

Dependency is defined directly on the raw syntax from `1a-preCaTT`.

```agda
mutual
  -- Semantic dependency between variables:
  -- `x` depends on `y` if they are equal, or if `x` occurs in the type of `y`.
  depends-on-var-var : ∀ {Γ} → Var Γ → Var Γ → Bool
  depends-on-var-var {Γ = Δ , A} vz vz = true
  depends-on-var-var {Γ = Δ , A} vz (vs y) = false
  depends-on-var-var {Γ = Δ , A} (vs x) vz = depends-on-var-ty x A
  depends-on-var-var {Γ = Δ , A} (vs x) (vs y) = depends-on-var-var x y

  -- Types depend on a variable if it appears in the base type or in either endpoint.
  depends-on-var-ty : ∀ {Γ} → Var Γ → Ty Γ → Bool
  depends-on-var-ty x ⋆ = false
  depends-on-var-ty x ([ A ] t ⇒ u) =
    depends-on-var-ty x A ∨ (depends-on-var-tm x t ∨ depends-on-var-tm x u)

  -- Terms depend on a variable via their variable case or via the stored substitution.
  depends-on-var-tm : ∀ {Γ} → Var Γ → Tm Γ → Bool
  depends-on-var-tm x (var y) = depends-on-var-var x y
  depends-on-var-tm x (coh-raw A u v σ) = depends-on-var-sub x σ

  -- Pointwise dependency of a substitution at a chosen codomain variable.
  depends-on-var-sub-at : ∀ {Γ Δ} → Var Γ → Sub Γ Δ → Var Δ → Bool
  depends-on-var-sub-at x ∅S ()
  depends-on-var-sub-at x (⟨ σ , t ⟩) vz = depends-on-var-tm x t
  depends-on-var-sub-at x (⟨ σ , t ⟩) (vs y) = depends-on-var-sub-at x σ y

  -- A substitution depends on `x` if any codomain variable image depends on `x`.
  depends-on-var-sub : ∀ {Γ Δ} → Var Γ → Sub Γ Δ → Bool
  depends-on-var-sub {Δ = Δ} x σ = ∃-var Δ (λ y → depends-on-var-sub-at x σ y)

-- A variable depends on itself.
dep-var-refl : ∀ {Γ} (x : Var Γ) → depends-on-var-var x x ≡ true
dep-var-refl vz = refl
dep-var-refl (vs x) = dep-var-refl x

abstract
  -- Pointwise substitution dependency is exactly dependency of the looked-up image.
  depends-on-var-sub-at-lookup :
    {Γ Δ : Ctx} (x : Var Γ) (σ : Sub Γ Δ) (y : Var Δ)
    → depends-on-var-sub-at x σ y ≡ depends-on-var-tm x (lookup y σ)
  depends-on-var-sub-at-lookup x (⟨ σ , t ⟩) vz = refl
  depends-on-var-sub-at-lookup x (⟨ σ , t ⟩) (vs y) =
    depends-on-var-sub-at-lookup x σ y

  -- Dependency of a substitution is stable under transport of its domain.
  depends-on-var-sub-transport :
    ∀ {Γ Γ' Δ} (e : Γ ≡ Γ') (x : Var Γ')
    {σ : Sub Γ Δ} {σ' : Sub Γ' Δ}
    → subst (λ Z → Sub Z Δ) e σ ≡ σ'
    → depends-on-var-sub (subst Var (sym e) x) σ
      ≡ depends-on-var-sub x σ'
  depends-on-var-sub-transport refl x refl = refl

  -- Lookup commutes with weakening of substitutions.
  lookup-wkSub :
    {Γ Δ : Ctx} {A0 : Ty Γ} (y : Var Δ) (σ : Sub Γ Δ)
    → lookup y (wkSub {A = A0} σ) ≡ wkTm (lookup y σ)
  lookup-wkSub vz (⟨ σ , t ⟩) = refl
  lookup-wkSub (vs y) (⟨ σ , t ⟩) = lookup-wkSub y σ

  -- Lookup through the identity substitution returns the same variable term.
  lookup-idS : ∀ {Γ} (x : Var Γ) → lookup x (idS Γ) ≡ var x
  lookup-idS {Γ = ∅} ()
  lookup-idS {Γ = Γ , A} vz = refl
  lookup-idS {Γ = Γ , A} (vs x) =
    trans (lookup-wkSub x (idS Γ))
          (cong wkTm (lookup-idS x))

  -- Under one-step weakening, the image of `x` under `wkSub (idS Γ)` is `vs x`.
  depends-on-var-sub-wk-self :
    {Γ : Ctx} {A0 : Ty Γ} (x : Var Γ)
    → depends-on-var-sub-at (vs x) (wkSub {A = A0} (idS Γ)) x ≡ true
  depends-on-var-sub-wk-self {Γ} {A0} x =
    trans
      (depends-on-var-sub-at-lookup (vs x) (wkSub {A = A0} (idS Γ)) x)
      (trans
        (cong (λ t → depends-on-var-tm (vs x) t)
              (trans (lookup-wkSub x (idS Γ))
                     (cong wkTm (lookup-idS x))))
        (dep-var-refl x))
```

## Congruence Helpers

At the raw level, congruence is simple structural congruence on constructors.

```agda
-- Congruence for hom-types
hom-cong3 : ∀ {Γ} {A A' : Ty Γ} {t t' u u' : Tm Γ}
  → (eA : A ≡ A') → (et : t ≡ t') → (eu : u ≡ u')
  → [ A ] t ⇒ u ≡ [ A' ] t' ⇒ u'
hom-cong3 refl refl refl = refl

-- Congruence for coh-raw
coh-raw-cong3 : ∀ {Γ Δ} {A A' : Ty Δ} {u u' v v' : Tm Δ} {σ σ' : Sub Γ Δ}
  → A ≡ A' → u ≡ u' → v ≡ v' → σ ≡ σ'
  → coh-raw A u v σ ≡ coh-raw A' u' v' σ'
coh-raw-cong3 refl refl refl refl = refl

-- Congruence for substitution extension
snoc-cong3 : ∀ {Γ Δ A} {σ σ' : Sub Γ Δ} {t t' : Tm Γ}
  → σ ≡ σ' → t ≡ t'
  → ⟨_,_⟩ {A = A} σ t ≡ ⟨_,_⟩ {A = A} σ' t'
snoc-cong3 refl refl = refl
```

## Predicate-Indexed Dependency

```agda
-- Type A depends on predicate X iff some selected variable occurs in A.
depends-on-X-ty : {Γ : Ctx} → (X : Var Γ → Bool) → Ty Γ → Bool
depends-on-X-ty {Γ} X A = ∃-var Γ (λ x → X x ∧ depends-on-var-ty x A)

-- Term t depends on predicate X iff some selected variable occurs in t.
depends-on-X-tm : {Γ : Ctx} → (X : Var Γ → Bool) → Tm Γ → Bool
depends-on-X-tm {Γ} X t = ∃-var Γ (λ x → X x ∧ depends-on-var-tm x t)

-- Witnessing: if P x = true then ∃-var Γ P = true.
∃-var-point-true :
  {Γ : Ctx} {P : Var Γ → Bool}
  → (x : Var Γ)
  → P x ≡ true
  → ∃-var Γ P ≡ true
∃-var-point-true {Γ = ∅} () px
∃-var-point-true {Γ = Γ , A} {P} vz px
  rewrite px = refl
∃-var-point-true {Γ = Γ , A} {P} (vs x) px =
  ∨-true-introʳ (∃-var-point-true x px)

-- Projection: if ∃-var Γ P = false then every witness point is false.
∃-var-point-false :
  {Γ : Ctx} {P : Var Γ → Bool}
  → (x : Var Γ)
  → ∃-var Γ P ≡ false
  → P x ≡ false
∃-var-point-false {Γ = ∅} () p
∃-var-point-false {Γ = Γ , A} {P} vz p =
  ∨-falseˡ p
∃-var-point-false {Γ = Γ , A} {P} (vs x) p =
  ∃-var-point-false x (∨-falseʳ p)

-- If every point is false, the existential fold is false.
∃-var-all-false :
  {Γ : Ctx} {P : Var Γ → Bool}
  → ((x : Var Γ) → P x ≡ false)
  → ∃-var Γ P ≡ false
∃-var-all-false {Γ = ∅} step = refl
∃-var-all-false {Γ = Γ , A} {P} step
  rewrite step vz
        | ∃-var-all-false {Γ = Γ} {P = λ x → P (vs x)} (λ x → step (vs x))
  = refl

-- Weakening preserves non-dependency (false direction), intrinsically.
{-# TERMINATING #-}
mutual
  -- A freshly inserted top variable never appears in a weakened type.
  depends-on-var-ty-vz-wk-false :
    ∀ {Γ} {A0 : Ty Γ} (B : Ty Γ)
    → depends-on-var-ty vz (wkTy {A = A0} B) ≡ false
  depends-on-var-ty-vz-wk-false ⋆ = refl
  depends-on-var-ty-vz-wk-false ([ A ] t ⇒ u) =
    trans
      (cong
        (λ z → z ∨ (depends-on-var-tm vz (wkTm t) ∨ depends-on-var-tm vz (wkTm u)))
        (depends-on-var-ty-vz-wk-false A))
      (trans
        (cong
          (λ z → false ∨ (z ∨ depends-on-var-tm vz (wkTm u)))
          (depends-on-var-tm-vz-wk-false t))
        (trans
          (cong (λ z → false ∨ (false ∨ z))
            (depends-on-var-tm-vz-wk-false u))
          refl))

  -- The same freshness fact for weakened terms.
  depends-on-var-tm-vz-wk-false :
    ∀ {Γ} {A0 : Ty Γ} (t : Tm Γ)
    → depends-on-var-tm vz (wkTm {A = A0} t) ≡ false
  depends-on-var-tm-vz-wk-false (var y) = refl
  depends-on-var-tm-vz-wk-false (coh-raw A u v σ) =
    depends-on-var-sub-vz-wk-false σ

  -- Freshness is checked pointwise when a weakened substitution is queried.
  depends-on-var-sub-at-vz-wk-false :
    ∀ {Γ Δ} {A0 : Ty Γ} (σ : Sub Γ Δ) (y : Var Δ)
    → depends-on-var-sub-at vz (wkSub {A = A0} σ) y ≡ false
  depends-on-var-sub-at-vz-wk-false {A0 = A0} σ y =
    trans
      (depends-on-var-sub-at-lookup vz (wkSub {A = A0} σ) y)
      (trans
        (cong (depends-on-var-tm vz) (lookup-wkSub {A0 = A0} y σ))
        (depends-on-var-tm-vz-wk-false (lookup y σ)))

  -- Therefore a weakened substitution is globally independent of the fresh top variable.
  depends-on-var-sub-vz-wk-false :
    ∀ {Γ Δ} {A0 : Ty Γ} (σ : Sub Γ Δ)
    → depends-on-var-sub vz (wkSub {A = A0} σ) ≡ false
  depends-on-var-sub-vz-wk-false {Δ = Δ} σ =
    ∃-var-all-false (depends-on-var-sub-at-vz-wk-false σ)

  -- If a weakened type ignores `vs x`, then the original type already ignored `x`.
  depends-on-var-ty-vs-wk-false :
    {Γ : Ctx} {A0 : Ty Γ} (x : Var Γ) (B : Ty Γ)
    → depends-on-var-ty (vs x) (wkTy {A = A0} B) ≡ false
    → depends-on-var-ty x B ≡ false
  depends-on-var-ty-vs-wk-false x ⋆ p = refl
  depends-on-var-ty-vs-wk-false x ([ A ] t ⇒ u) p
    with depends-on-var-ty (vs x) (wkTy A) in da
       | depends-on-var-tm (vs x) (wkTm t) in dt
       | depends-on-var-tm (vs x) (wkTm u) in du
  ... | true  | _     | _     =
    true≠false (trans (sym da)
      (∨3-falseˡ
        {a = depends-on-var-ty (vs x) (wkTy A)}
        {b = depends-on-var-tm (vs x) (wkTm t)}
        {c = depends-on-var-tm (vs x) (wkTm u)} p))
  ... | false | true  | _     =
    true≠false (trans (sym dt)
      (∨3-falseᵐ
        {a = depends-on-var-ty (vs x) (wkTy A)}
        {b = depends-on-var-tm (vs x) (wkTm t)}
        {c = depends-on-var-tm (vs x) (wkTm u)} p))
  ... | false | false | true  =
    true≠false (trans (sym du)
      (∨3-falseʳ
        {a = depends-on-var-ty (vs x) (wkTy A)}
        {b = depends-on-var-tm (vs x) (wkTm t)}
        {c = depends-on-var-tm (vs x) (wkTm u)} p))
  ... | false | false | false
    rewrite depends-on-var-ty-vs-wk-false x A
              (∨3-falseˡ
                {a = depends-on-var-ty (vs x) (wkTy A)}
                {b = depends-on-var-tm (vs x) (wkTm t)}
                {c = depends-on-var-tm (vs x) (wkTm u)} p)
          | depends-on-var-tm-vs-wk-false x t
              (∨3-falseᵐ
                {a = depends-on-var-ty (vs x) (wkTy A)}
                {b = depends-on-var-tm (vs x) (wkTm t)}
                {c = depends-on-var-tm (vs x) (wkTm u)} p)
          | depends-on-var-tm-vs-wk-false x u
              (∨3-falseʳ
                {a = depends-on-var-ty (vs x) (wkTy A)}
                {b = depends-on-var-tm (vs x) (wkTm t)}
                {c = depends-on-var-tm (vs x) (wkTm u)} p)
          | da | dt | du
    = refl

  -- The term-level version of the previous downward transport.
  depends-on-var-tm-vs-wk-false :
    {Γ : Ctx} {A0 : Ty Γ} (x : Var Γ) (t : Tm Γ)
    → depends-on-var-tm (vs x) (wkTm {A = A0} t) ≡ false
    → depends-on-var-tm x t ≡ false
  depends-on-var-tm-vs-wk-false x (var y) p = p
  depends-on-var-tm-vs-wk-false x (coh-raw A u v σ) pfalse =
    depends-on-var-sub-vs-wk-false x σ pfalse

  -- Pointwise non-dependency descends through weakening of substitutions.
  depends-on-var-sub-at-vs-wk-false :
    {Γ Δ : Ctx} {A0 : Ty Γ}
    (x : Var Γ) (σ : Sub Γ Δ) (y : Var Δ)
    → depends-on-var-sub-at (vs x) (wkSub {A = A0} σ) y ≡ false
    → depends-on-var-sub-at x σ y ≡ false
  depends-on-var-sub-at-vs-wk-false {A0 = A0} x σ y p =
    trans
      (depends-on-var-sub-at-lookup x σ y)
      (depends-on-var-tm-vs-wk-false x (lookup y σ)
        (trans
          (sym
            (trans
              (depends-on-var-sub-at-lookup (vs x) (wkSub {A = A0} σ) y)
              (cong (depends-on-var-tm (vs x)) (lookup-wkSub {A0 = A0} y σ))))
          p))

  -- Hence global non-dependency also descends through weakening of substitutions.
  depends-on-var-sub-vs-wk-false :
    {Γ Δ : Ctx} {A0 : Ty Γ} (x : Var Γ) (σ : Sub Γ Δ)
    → depends-on-var-sub (vs x) (wkSub {A = A0} σ) ≡ false
    → depends-on-var-sub x σ ≡ false
  depends-on-var-sub-vs-wk-false {Δ = Δ} {A0 = A0} x σ p =
    ∃-var-all-false step
    where
      step : (y : Var Δ) → depends-on-var-sub-at x σ y ≡ false
      step y = depends-on-var-sub-at-vs-wk-false {A0 = A0} x σ y (∃-var-point-false y p)

-- Weakening commutes with dependency: the dependency of `vs x` on a weakened
-- object equals the dependency of `x` on the original object.
{-# TERMINATING #-}
mutual
  dep-ty-vs-wk :
    {Γ : Ctx} {A0 : Ty Γ} (x : Var Γ) (B : Ty Γ)
    → depends-on-var-ty (vs x) (wkTy {A = A0} B) ≡ depends-on-var-ty x B
  dep-ty-vs-wk x ⋆ = refl
  dep-ty-vs-wk x ([ A ] t ⇒ u) =
    cong₂ (λ a bc → a ∨ bc)
      (dep-ty-vs-wk x A)
      (cong₂ _∨_ (dep-tm-vs-wk x t) (dep-tm-vs-wk x u))

  dep-tm-vs-wk :
    {Γ : Ctx} {A0 : Ty Γ} (x : Var Γ) (t : Tm Γ)
    → depends-on-var-tm (vs x) (wkTm {A = A0} t) ≡ depends-on-var-tm x t
  dep-tm-vs-wk x (var y) = refl
  dep-tm-vs-wk x (coh-raw A u v σ) = dep-sub-vs-wk x σ

  dep-sub-at-vs-wk :
    {Γ Δ : Ctx} {A0 : Ty Γ} (x : Var Γ) (σ : Sub Γ Δ) (y : Var Δ)
    → depends-on-var-sub-at (vs x) (wkSub {A = A0} σ) y
      ≡ depends-on-var-sub-at x σ y
  dep-sub-at-vs-wk x (⟨ σ , t ⟩) vz = dep-tm-vs-wk x t
  dep-sub-at-vs-wk x (⟨ σ , t ⟩) (vs y) = dep-sub-at-vs-wk x σ y

  dep-sub-vs-wk :
    {Γ Δ : Ctx} {A0 : Ty Γ} (x : Var Γ) (σ : Sub Γ Δ)
    → depends-on-var-sub (vs x) (wkSub {A = A0} σ)
      ≡ depends-on-var-sub x σ
  dep-sub-vs-wk {Δ = ∅} x ∅S = refl
  dep-sub-vs-wk {Δ = Δ , B} x (⟨ σ , t ⟩) =
    cong₂ _∨_ (dep-tm-vs-wk x t)
              (dep-sub-vs-wk x σ)

-- If A is independent of X, every variable used by A lies outside X.
indep-outside : {Γ : Ctx} → (X : Var Γ → Bool) → (A : Ty Γ)
  → depends-on-X-ty X A ≡ false
  → (x : Var Γ) → depends-on-var-ty x A ≡ true → X x ≡ false
indep-outside {Γ} X A indep x dx =
  ∧-falseˡ-from-trueʳ (∃-var-point-false x indep) dx

-- Term analogue of indep-outside.
indep-outside-tm : {Γ : Ctx} → (X : Var Γ → Bool) → (t : Tm Γ)
  → depends-on-X-tm X t ≡ false
  → (x : Var Γ) → depends-on-var-tm x t ≡ true → X x ≡ false
indep-outside-tm {Γ} X t indep x dx =
  ∧-falseˡ-from-trueʳ (∃-var-point-false x indep) dx

-- If a hom-type is independent of X, then its base type is independent of X.
hom-type-indep-base :
  {Γ : Ctx}
  → (X : Var Γ → Bool)
  → {A : Ty Γ} {u v : Tm Γ}
  → depends-on-X-ty X ([ A ] u ⇒ v) ≡ false
  → depends-on-X-ty X A ≡ false
hom-type-indep-base {Γ} X {A} {u} {v} indepHom = ∃-var-all-false step
  where
    step : (x : Var Γ) → (X x ∧ depends-on-var-ty x A) ≡ false
    step x with X x in eqX | depends-on-var-ty x A in eqA
    ... | false | depA = refl
    ... | true | false = refl
    ... | true | true =
      true≠false
        (trans
          (sym eqX)
          (indep-outside X ([ A ] u ⇒ v) indepHom x
            (∨-true-introˡ eqA)))
```

## Agreement Lemmas

If two substitutions agree on all variables that a type/term/substitution
depends on, then substituting by either gives the same result.

```agda
mutual
  sub-agree-ty : ∀ {Γ Δ} (A : Ty Γ) (σ τ : Sub Δ Γ)
    → ((x : Var Γ) → depends-on-var-ty x A ≡ true → var x [ σ ]t ≡ var x [ τ ]t)
    → A [ σ ]T ≡ A [ τ ]T
  sub-agree-ty ⋆ σ τ agree = refl
  sub-agree-ty ([ B ] t ⇒ u) σ τ agree =
    hom-cong3
      (sub-agree-ty B σ τ (λ x dx → agree x
        (∨-true-introˡ {c = depends-on-var-tm x t ∨ depends-on-var-tm x u} dx)))
      (sub-agree-tm t σ τ (λ x dx → agree x
        (∨-true-introʳ {b = depends-on-var-ty x B}
          (∨-true-introˡ {c = depends-on-var-tm x u} dx))))
      (sub-agree-tm u σ τ (λ x dx → agree x
        (∨-true-introʳ {b = depends-on-var-ty x B}
          (∨-true-introʳ {b = depends-on-var-tm x t} dx))))

  sub-agree-tm : ∀ {Γ Δ} (t : Tm Γ) (σ τ : Sub Δ Γ)
    → ((x : Var Γ) → depends-on-var-tm x t ≡ true → var x [ σ ]t ≡ var x [ τ ]t)
    → t [ σ ]t ≡ t [ τ ]t
  sub-agree-tm (var y) σ τ agree = agree y (dep-var-refl y)
  sub-agree-tm (coh-raw A u v γ) σ τ agree =
    coh-raw-cong3 refl refl refl (sub-agree-sub γ σ τ agree)

  sub-agree-sub : ∀ {Γ Δ Ξ} (γ : Sub Γ Δ) (σ τ : Sub Ξ Γ)
    → ((x : Var Γ) → depends-on-var-sub x γ ≡ true → var x [ σ ]t ≡ var x [ τ ]t)
    → γ ∘ σ ≡ γ ∘ τ
  sub-agree-sub ∅S σ τ agree = refl
  sub-agree-sub (⟨ γ , s ⟩) σ τ agree =
    snoc-cong3
      (sub-agree-sub γ σ τ (λ x dx → agree x (∨-true-introʳ dx)))
      (sub-agree-tm s σ τ (λ x dx → agree x (∨-true-introˡ dx)))
```

## Dependency Through Variable Typing

If a variable appears in the declared type of another variable, then it
semantically depends on that variable.

```agda
dep-var-to-type→dep-var :
  ∀ {Γ} (x y : Var Γ)
  → depends-on-var-ty x (var-to-type y) ≡ true
  → depends-on-var-var x y ≡ true
dep-var-to-type→dep-var {Γ = Γ , A} vz vz h =
  true≠false (trans (sym h) (depends-on-var-ty-vz-wk-false A))
dep-var-to-type→dep-var {Γ = Γ , A} vz (vs y) h =
  true≠false (trans (sym h) (depends-on-var-ty-vz-wk-false (var-to-type y)))
dep-var-to-type→dep-var {Γ = Γ , A} (vs x) vz h =
  trans (sym (dep-ty-vs-wk {A0 = A} x A)) h
dep-var-to-type→dep-var {Γ = Γ , A} (vs x) (vs y) h =
  dep-var-to-type→dep-var x y
    (trans (sym (dep-ty-vs-wk {A0 = A} x (var-to-type y))) h)
```

## Reverse Agreement (Dependency Through Substitution)

If a substituted type/term depends on a variable `x`, then the substitution
itself depends on `x`. This is the constructive converse of the agreement
lemmas.

```agda
{-# TERMINATING #-}
mutual
  dep-ty-sub→dep-sub :
    ∀ {Γ Δ} (x : Var Γ) (A : Ty Δ) (σ : Sub Γ Δ)
    → depends-on-var-ty x (A [ σ ]T) ≡ true
    → depends-on-var-sub x σ ≡ true
  dep-ty-sub→dep-sub x ⋆ σ ()
  dep-ty-sub→dep-sub x ([ B ] u ⇒ v) σ h = go h
    where
      go : depends-on-var-ty x (B [ σ ]T)
           ∨ (depends-on-var-tm x (u [ σ ]t) ∨ depends-on-var-tm x (v [ σ ]t))
           ≡ true
         → depends-on-var-sub x σ ≡ true
      go h'
        with depends-on-var-ty x (B [ σ ]T) in eqB
      ... | true = dep-ty-sub→dep-sub x B σ eqB
      ... | false
        with depends-on-var-tm x (u [ σ ]t) in eqU
      ... | true = dep-tm-sub→dep-sub x u σ eqU
      ... | false = dep-tm-sub→dep-sub x v σ h'

  dep-tm-sub→dep-sub :
    ∀ {Γ Δ} (x : Var Γ) (t : Tm Δ) (σ : Sub Γ Δ)
    → depends-on-var-tm x (t [ σ ]t) ≡ true
    → depends-on-var-sub x σ ≡ true
  dep-tm-sub→dep-sub x (var vz) (⟨ σ , t ⟩) h = ∨-true-introˡ h
  dep-tm-sub→dep-sub x (var (vs y)) (⟨ σ , t ⟩) h =
    ∨-true-introʳ (dep-tm-sub→dep-sub x (var y) σ h)
  dep-tm-sub→dep-sub x (coh-raw A u v τ) σ h =
    dep-sub-comp→dep-sub x τ σ h

  dep-sub-comp→dep-sub :
    ∀ {Γ Δ Ξ} (x : Var Γ) (τ : Sub Δ Ξ) (σ : Sub Γ Δ)
    → depends-on-var-sub x (τ ∘ σ) ≡ true
    → depends-on-var-sub x σ ≡ true
  dep-sub-comp→dep-sub x ∅S σ ()
  dep-sub-comp→dep-sub x (⟨ τ , t ⟩) σ h = go h
    where
      go : depends-on-var-tm x (t [ σ ]t) ∨ depends-on-var-sub x (τ ∘ σ)
           ≡ true
         → depends-on-var-sub x σ ≡ true
      go h'
        with depends-on-var-tm x (t [ σ ]t) in eqT
      ... | true = dep-tm-sub→dep-sub x t σ eqT
      ... | false = dep-sub-comp→dep-sub x τ σ h'
```

## Dependency Through Typing

If a variable appears in the type of a term, then it appears in the term
itself.

```agda
dep-tyOf→dep-tm :
  ∀ {Γ} (x : Var Γ) (t : Tm Γ)
  → depends-on-var-ty x (tyOf t) ≡ true
  → depends-on-var-tm x t ≡ true
dep-tyOf→dep-tm x (var y) h = dep-var-to-type→dep-var x y h
dep-tyOf→dep-tm x (coh-raw A u v σ) h = dep-ty-sub→dep-sub x ([ A ] u ⇒ v) σ h
```
