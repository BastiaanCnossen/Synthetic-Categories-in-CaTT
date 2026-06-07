# 2e-FunctorialityContexts: Typed Functoriality Contexts, Inclusions, and Agreement

This module is the typed V8 functoriality-context layer.

Given a context `Γ` and a selector `X : Var Γ → Bool` of locally maximal
variables, it constructs:

- the functoriality context `Γ ↑ X`
- the negative inclusion `in⁻ : Γ ↑ X → Γ`
- the positive inclusion `in⁺ : Γ ↑ X → Γ`
- agreement lemmas (`agree-var`, `agree-tm`, `agree-ty`) showing that `in⁻`
  and `in⁺` coincide on variables, terms, and types independent of `X`

The recursive branch structure mirrors raw `1e-FunctorialityContexts`, but each
branch is packaged directly as a typed `Ctx` or `Sub`. The proof burden is
isolated in `2d-FunctorialityContextHelpers`, whose public API consists exactly
of the well-formedness lemmas needed to build the typed branch constructors.

```agda
module 2e-FunctorialityContexts where

open import Agda.Builtin.Equality
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)

import 1a-preCaTT as Pre
import 1c-Pasting as PrePs
import 1e-FunctorialityContexts as RawFC
import 1f-FunctorialityPasting as RawFP
open import 2b-Wrappers
open import 2d-FunctorialityContextHelpers

infixl 8 _↑_
```

## Thin Wrapper Layer

```agda
is-local-max : {Γ : Ctx} → Var Γ → Bool
is-local-max {Γ} = RawFC.is-local-max {Γ = Raw-Ctx Γ}

all-local-max : {Γ : Ctx} → (Var Γ → Bool) → Bool
all-local-max {Γ} X = RawFC.all-local-max {Γ = Raw-Ctx Γ} X

dropLast : {Γ : Ctx} {A : Ty Γ} → (Var (Γ , A) → Bool) → Var Γ → Bool
dropLast {Γ} {A} X x = X (succ {Γ} {A} x)

dropLast2 :
  {Γ : Ctx} {A : Ty Γ} {B : Ty (Γ , A)}
  → (Var ((Γ , A) , B) → Bool) → Var Γ → Bool
dropLast2 {Γ} {A} {B} X x = X (succ {Γ , A} {B} (succ {Γ} {A} x))

local-max-tyOf-implies-tm :
  {Γ : Ctx}
  → (x : Var Γ) → (t : Tm Γ)
  → is-local-max {Γ = Γ} x ≡ true
  → depends-on-var-ty {Γ = Γ} x (tyOf {Γ = Γ} t) ≡ true
  → depends-on-var-tm {Γ = Γ} x t ≡ true
local-max-tyOf-implies-tm {Γ} x t lm dep = dep-tyOf→dep-tm {Γ = Γ} x t dep

inv-img : {Γ Δ : Ctx} → Sub Γ Δ → (Var Γ → Bool) → (Var Δ → Bool)
inv-img {Γ} {Δ} σ X y =
  ∃-var Γ (λ x → X x ∧ depends-on-var-sub-at {Γ = Γ} {Δ = Δ} x σ y)

private
  local-max-restrict :
    {Γ : Ctx} {A : Ty Γ}
    → (X : Var (Γ , A) → Bool)
    → all-local-max {Γ = Γ , A} X ≡ true
    → all-local-max {Γ = Γ} (dropLast {Γ = Γ} {A = A} X) ≡ true
  local-max-restrict {Γ} {A} X lm =
    RawFC.local-max-restrict {Γ = Raw-Ctx Γ} {A = Raw-Ty A} X lm

  local-max-type-indep :
    {Γ : Ctx} {A : Ty Γ}
    → (X : Var (Γ , A) → Bool)
    → all-local-max {Γ = Γ , A} X ≡ true
    → depends-on-X-ty {Γ = Γ} (dropLast {Γ = Γ} {A = A} X) A ≡ false
  local-max-type-indep {Γ} {A} X lm =
    RawFC.local-max-type-indep {Γ = Raw-Ctx Γ} {A = Raw-Ty A} X lm

  lookup-∘ :
    ∀ {Γ Δ Θ} (x : Var Θ) (τ : Sub Δ Θ) (σ : Sub Γ Δ)
    → lookup x (τ ∘ σ) ≡ (lookup x τ) [ σ ]t
  lookup-∘ {Γ} x τ σ =
    Tm-ext
      {Γ = Γ}
      (Pre.lookup-∘ x (Raw-Sub τ) (Raw-Sub σ))
```

## Pasting Preservation Wrapper

```agda
functoriality-preserves-pasting :
  {Γ : Ctx}
  → (Γps : CtxPs Γ)
  → (X : Var Γ → Bool)
  → all-local-max {Γ = Γ} X ≡ true
  → PrePs.CtxPs (RawFC._↑_ (Raw-Ctx Γ) X)
functoriality-preserves-pasting {Γ} Γps X lm =
  RawFP.func-pasting-raw {Γ = Raw-Ctx Γ} Γps X lm
```

## Non-Recursive Step Constructors

```agda
in⁻-false-step :
  ∀ {Γ Δ}
  (A : Ty Γ)
  (ρ : Sub Δ Γ)
  → Sub (Δ , (A [ ρ ]T)) (Γ , A)
in⁻-false-step {Δ = Δ} A ρ =
  ⟨ ρ ∘ wk , vz {Γ = Δ} {A = A [ ρ ]T} ⟩∶[
    snoc-vz-after-wk-typed A ρ
  ]

in⁻-true-step :
  ∀ {Γ Δ}
  (A : Ty Γ)
  (ρ : Sub Δ Γ)
  → Sub (splitCtx A ρ) (Γ , A)
in⁻-true-step A ρ =
  ⟨ ρ ∘ splitWk³ A ρ , split-src A ρ ⟩∶[
    snoc-src-after-split-typed A ρ
  ]

in⁺-false-step :
  ∀ {Γ Δ}
  (A : Ty Γ)
  (ρ : Sub Δ Γ)
  (B : Ty Δ)
  (e : B ≡ A [ ρ ]T)
  → Sub (Δ , B) (Γ , A)
in⁺-false-step {Γ = Γ} {Δ = Δ} A ρ B e =
  subst (λ C → Sub (Δ , C) (Γ , A)) (sym e)
    (⟨ ρ ∘ wk , vz {Γ = Δ} {A = A [ ρ ]T} ⟩∶[
       snoc-vz-after-wk-typed A ρ
     ])

in⁺-true-step :
  ∀ {Γ Δ}
  (A : Ty Γ)
  (ρ : Sub Δ Γ)
  (B : Ty Δ)
  (e : B ≡ A [ ρ ]T)
  → Sub (split-step-ctx B) (Γ , A)
in⁺-true-step {Γ} {Δ} A ρ B e =
  subst (λ C → Sub (split-step-ctx C) (Γ , A)) (sym e)
    (⟨ ρ ∘ wk³ , split-tgt A ρ ⟩∶[
       snoc-tgt-after-split-typed A ρ
     ])
```

## Lookup Lemmas and Non-Recursive Agreement Steps

```agda
abstract
  lookup-vz-in⁻-false-step :
    ∀ {Γ Δ}
    (A : Ty Γ)
    (ρ : Sub Δ Γ)
    → vz {Γ = Δ} {A = A [ ρ ]T}
      ≡ lookup (zero {Γ = Γ} {A = A}) (in⁻-false-step A ρ)
  lookup-vz-in⁻-false-step A ρ = refl

  lookup-vs-in⁻-false-step :
    ∀ {Γ Δ}
    (A : Ty Γ)
    (ρ : Sub Δ Γ)
    (x : Var Γ)
    → lookup (succ {Γ = Γ} {A = A} x) (in⁻-false-step A ρ) ≡ (lookup x ρ) [ wk ]t
  lookup-vs-in⁻-false-step A ρ x = lookup-∘ x ρ wk

  lookup-vs-in⁻-true-step :
    ∀ {Γ Δ}
    (A : Ty Γ)
    (ρ : Sub Δ Γ)
    (x : Var Γ)
    → lookup (succ {Γ = Γ} {A = A} x) (in⁻-true-step A ρ)
      ≡ (lookup x ρ) [ splitWk³ A ρ ]t
  lookup-vs-in⁻-true-step A ρ x =
    lookup-∘ x ρ (splitWk³ A ρ)

  lookup-vz-in⁺-false-step :
    ∀ {Γ Δ}
    (A : Ty Γ)
    (ρ : Sub Δ Γ)
    (B : Ty Δ)
    (e : B ≡ A [ ρ ]T)
    → vz {Γ = Δ} {A = B}
      ≡ lookup (zero {Γ = Γ} {A = A}) (in⁺-false-step A ρ B e)
  lookup-vz-in⁺-false-step A ρ .(A [ ρ ]T) refl = refl

  lookup-vs-in⁺-false-step :
    ∀ {Γ Δ}
    (A : Ty Γ)
    (ρ : Sub Δ Γ)
    (B : Ty Δ)
    (e : B ≡ A [ ρ ]T)
    (x : Var Γ)
    → lookup (succ {Γ = Γ} {A = A} x) (in⁺-false-step A ρ B e) ≡ (lookup x ρ) [ wk ]t
  lookup-vs-in⁺-false-step A ρ .(A [ ρ ]T) refl x = lookup-∘ x ρ wk

  lookup-vs-in⁺-true-step :
    ∀ {Γ Δ}
    (A : Ty Γ)
    (ρ : Sub Δ Γ)
    (B : Ty Δ)
    (e : B ≡ A [ ρ ]T)
    (x : Var Γ)
    → lookup (succ {Γ = Γ} {A = A} x) (in⁺-true-step A ρ B e) ≡ (lookup x ρ) [ wk³ ]t
  lookup-vs-in⁺-true-step A ρ .(A [ ρ ]T) refl x = lookup-∘ x ρ wk³

agree-var-vz-false-step :
  ∀ {Γ Δ}
  (A : Ty Γ)
  (ρ⁻ ρ⁺ : Sub Δ Γ)
  (e⁺ : A [ ρ⁻ ]T ≡ A [ ρ⁺ ]T)
  → (vz {Γ = Γ} {A = A}) [ in⁻-false-step A ρ⁻ ]t
    ≡ (vz {Γ = Γ} {A = A}) [ in⁺-false-step A ρ⁺ (A [ ρ⁻ ]T) e⁺ ]t

agree-var-vs-false-step :
  ∀ {Γ Δ}
  (A : Ty Γ)
  (ρ⁻ ρ⁺ : Sub Δ Γ)
  (e⁺ : A [ ρ⁻ ]T ≡ A [ ρ⁺ ]T)
  (y : Var Γ)
  (ih : (var y) [ ρ⁻ ]t ≡ (var y) [ ρ⁺ ]t)
  → (var (succ {Γ = Γ} {A = A} y)) [ in⁻-false-step A ρ⁻ ]t
    ≡ (var (succ {Γ = Γ} {A = A} y)) [ in⁺-false-step A ρ⁺ (A [ ρ⁻ ]T) e⁺ ]t

agree-var-vs-true-step :
  ∀ {Γ Δ}
  (A : Ty Γ)
  (ρ⁻ ρ⁺ : Sub Δ Γ)
  (e⁺ : A [ ρ⁻ ]T ≡ A [ ρ⁺ ]T)
  (y : Var Γ)
  (ih : (var y) [ ρ⁻ ]t ≡ (var y) [ ρ⁺ ]t)
  → (var (succ {Γ = Γ} {A = A} y)) [ in⁻-true-step A ρ⁻ ]t
    ≡ (var (succ {Γ = Γ} {A = A} y)) [ in⁺-true-step A ρ⁺ (A [ ρ⁻ ]T) e⁺ ]t

abstract
  agree-var-vz-false-step A ρ⁻ ρ⁺ e⁺ =
    trans
      (sym (lookup-vz-in⁻-false-step A ρ⁻))
      (lookup-vz-in⁺-false-step A ρ⁺ (A [ ρ⁻ ]T) e⁺)

  agree-var-vs-false-step A ρ⁻ ρ⁺ e⁺ y ih =
    trans
      (lookup-vs-in⁻-false-step A ρ⁻ y)
      (trans
        (cong (_[ wk ]t) ih)
        (sym (lookup-vs-in⁺-false-step A ρ⁺ (A [ ρ⁻ ]T) e⁺ y)))

  agree-var-vs-true-step A ρ⁻ ρ⁺ e⁺ y ih =
    trans
      (lookup-vs-in⁻-true-step A ρ⁻ y)
      (trans
        (cong (_[ wk³ ]t) ih)
        (sym (lookup-vs-in⁺-true-step A ρ⁺ (A [ ρ⁻ ]T) e⁺ y)))
```

## Functoriality Context, Inclusions, and Agreement

```agda
{-# TERMINATING #-}
mutual
  ↑-step : ∀ {Γ} (A : Ty Γ) (b : Bool) (X0 : Var Γ → Bool) → Ctx
  ↑-step {Γ} A false X0 = (Γ ↑ X0) , (A [ in⁻ Γ X0 ]T)
  ↑-step {Γ} A true X0 = split-step-ctx A'
    where
      A' : Ty (Γ ↑ X0)
      A' = A [ in⁻ Γ X0 ]T

  _↑_ : (Γ : Ctx) → (Var Γ → Bool) → Ctx
  _↑_ Γ X with ctx-view Γ
  ... | ∅-view = ∅
  ... | snoc-view {Γ = Γ'} A = ↑-step A (X z) X0
    where
      z : Var (Γ' , A)
      z = zero {Γ = Γ'} {A = A}

      X0 : Var Γ' → Bool
      X0 x = X (succ {Γ = Γ'} {A = A} x)

  in⁻-step :
    ∀ {Γ} (A : Ty Γ) (b : Bool) (X0 : Var Γ → Bool)
    → Sub (↑-step A b X0) (Γ , A)
  in⁻-step {Γ} A false X0 = in⁻-false-step A (in⁻ Γ X0)
  in⁻-step {Γ} A true X0 = in⁻-true-step A (in⁻ Γ X0)

  in⁻ : (Γ : Ctx) → (X : Var Γ → Bool) → Sub (Γ ↑ X) Γ
  in⁻ Γ X with ctx-view Γ
  ... | ∅-view = ∅S
  ... | snoc-view {Γ = Γ'} A = in⁻-step A (X z) X0
    where
      z : Var (Γ' , A)
      z = zero {Γ = Γ'} {A = A}

      X0 : Var Γ' → Bool
      X0 x = X (succ {Γ = Γ'} {A = A} x)

  in⁺-step :
    ∀ {Γ} (A : Ty Γ) (b : Bool) (X0 : Var Γ → Bool)
    → (lm' : all-local-max {Γ = Γ} X0 ≡ true)
    → depends-on-X-ty {Γ = Γ} X0 A ≡ false
    → Sub (↑-step A b X0) (Γ , A)
  in⁺-step {Γ} A false X0 lm' indep =
    in⁺-false-step A ρ⁺ (A [ in⁻ Γ X0 ]T) e⁺
    where
      ρ⁺ : Sub (Γ ↑ X0) Γ
      ρ⁺ = in⁺ Γ X0 lm'

      e⁺ : A [ in⁻ Γ X0 ]T ≡ A [ ρ⁺ ]T
      e⁺ = agree-ty Γ X0 lm' A indep
  in⁺-step {Γ} A true X0 lm' indep =
    in⁺-true-step A ρ⁺ (A [ in⁻ Γ X0 ]T) e⁺
    where
      ρ⁺ : Sub (Γ ↑ X0) Γ
      ρ⁺ = in⁺ Γ X0 lm'

      e⁺ : A [ in⁻ Γ X0 ]T ≡ A [ ρ⁺ ]T
      e⁺ = agree-ty Γ X0 lm' A indep

  in⁺ :
    (Γ : Ctx) → (X : Var Γ → Bool)
    → all-local-max {Γ = Γ} X ≡ true → Sub (Γ ↑ X) Γ
  in⁺ Γ X lm with ctx-view Γ
  ... | ∅-view = ∅S
  ... | snoc-view {Γ = Γ'} A =
    in⁺-step A (X z) X0
      (local-max-restrict {Γ = Γ'} {A = A} X lm)
      (local-max-type-indep {Γ = Γ'} {A = A} X lm)
    where
      z : Var (Γ' , A)
      z = zero {Γ = Γ'} {A = A}

      X0 : Var Γ' → Bool
      X0 x = X (succ {Γ = Γ'} {A = A} x)

  agree-ty :
    (Γ : Ctx) → (X : Var Γ → Bool) → (lm : all-local-max {Γ = Γ} X ≡ true)
    → (A : Ty Γ) → depends-on-X-ty {Γ = Γ} X A ≡ false
    → A [ in⁻ Γ X ]T ≡ A [ in⁺ Γ X lm ]T
  agree-ty Γ X lm A indep =
    sub-agree-ty A (in⁻ Γ X) (in⁺ Γ X lm)
      (λ x dx → agree-var Γ X lm x (indep-outside X A indep x dx))

  agree-tm :
    (Γ : Ctx) → (X : Var Γ → Bool) → (lm : all-local-max {Γ = Γ} X ≡ true)
    → (t : Tm Γ) → depends-on-X-tm {Γ = Γ} X t ≡ false
    → t [ in⁻ Γ X ]t ≡ t [ in⁺ Γ X lm ]t
  agree-tm Γ X lm t indep =
    sub-agree-tm t (in⁻ Γ X) (in⁺ Γ X lm)
      (λ x dx → agree-var Γ X lm x (indep-outside-tm X t indep x dx))

  agree-var-vz-step' :
    ∀ {Γ} (A : Ty Γ) (b : Bool) (X0 : Var Γ → Bool)
    (lm' : all-local-max {Γ = Γ} X0 ≡ true)
    (indep : depends-on-X-ty {Γ = Γ} X0 A ≡ false)
    → b ≡ false
    → (vz {Γ = Γ} {A = A}) [ in⁻-step A b X0 ]t
      ≡ (vz {Γ = Γ} {A = A}) [ in⁺-step A b X0 lm' indep ]t
  agree-var-vz-step' {Γ} A false X0 lm' indep refl =
    agree-var-vz-false-step A (in⁻ Γ X0) (in⁺ Γ X0 lm') (agree-ty Γ X0 lm' A indep)
  agree-var-vz-step' A true X0 lm' indep ()

  agree-var-vs-step' :
    ∀ {Γ} (A : Ty Γ) (b : Bool) (X0 : Var Γ → Bool)
    (lm' : all-local-max {Γ = Γ} X0 ≡ true)
    (indep : depends-on-X-ty {Γ = Γ} X0 A ≡ false)
    (y : Var Γ)
    → X0 y ≡ false
    → (var (succ {Γ = Γ} {A = A} y)) [ in⁻-step A b X0 ]t
      ≡ (var (succ {Γ = Γ} {A = A} y)) [ in⁺-step A b X0 lm' indep ]t
  agree-var-vs-step' {Γ} A false X0 lm' indep y px =
    agree-var-vs-false-step A (in⁻ Γ X0) (in⁺ Γ X0 lm') (agree-ty Γ X0 lm' A indep) y ih
    where
      ih : (var y) [ in⁻ Γ X0 ]t ≡ (var y) [ in⁺ Γ X0 lm' ]t
      ih = agree-var Γ X0 lm' y px
  agree-var-vs-step' {Γ} A true X0 lm' indep y px =
    agree-var-vs-true-step A (in⁻ Γ X0) (in⁺ Γ X0 lm') (agree-ty Γ X0 lm' A indep) y ih
    where
      ih : (var y) [ in⁻ Γ X0 ]t ≡ (var y) [ in⁺ Γ X0 lm' ]t
      ih = agree-var Γ X0 lm' y px

  agree-var-empty :
    (X : Var ∅ → Bool) → (lm : all-local-max {Γ = ∅} X ≡ true)
    → (x : Var ∅) → X x ≡ false
    → (var x) [ in⁻ ∅ X ]t ≡ (var x) [ in⁺ ∅ X lm ]t
  agree-var-empty X lm () px

  agree-var-snoc :
    ∀ {Γ} (A : Ty Γ)
    → (X : Var (Γ , A) → Bool) → (lm : all-local-max {Γ = Γ , A} X ≡ true)
    → (x : Var (Γ , A)) → X x ≡ false
    → (var x) [ in⁻ (Γ , A) X ]t ≡ (var x) [ in⁺ (Γ , A) X lm ]t
  agree-var-snoc {Γ} A X lm Pre.vz px =
    agree-var-vz-step' A (X z) X0
      (local-max-restrict {Γ = Γ} {A = A} X lm)
      (local-max-type-indep {Γ = Γ} {A = A} X lm)
      px
    where
      z : Var (Γ , A)
      z = zero {Γ = Γ} {A = A}

      X0 : Var Γ → Bool
      X0 x = X (succ {Γ = Γ} {A = A} x)
  agree-var-snoc {Γ} A X lm (Pre.vs y) px =
    agree-var-vs-step' A (X z) X0
      (local-max-restrict {Γ = Γ} {A = A} X lm)
      (local-max-type-indep {Γ = Γ} {A = A} X lm)
      y px
    where
      z : Var (Γ , A)
      z = zero {Γ = Γ} {A = A}

      X0 : Var Γ → Bool
      X0 x = X (succ {Γ = Γ} {A = A} x)

  agree-var :
    (Γ : Ctx) → (X : Var Γ → Bool) → (lm : all-local-max {Γ = Γ} X ≡ true)
    → (x : Var Γ) → X x ≡ false
    → (var x) [ in⁻ Γ X ]t ≡ (var x) [ in⁺ Γ X lm ]t
  agree-var Γ X lm x px with ctx-view Γ
  ... | ∅-view = agree-var-empty X lm x px
  ... | snoc-view {Γ = Γ'} A = agree-var-snoc {Γ = Γ'} A X lm x px
```
