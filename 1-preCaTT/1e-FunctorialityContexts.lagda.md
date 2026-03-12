# 1e-FunctorialityContexts: Pre-Syntax Functoriality Contexts

This module contains the context-level part of pre-syntax functoriality. For a context `Γ` and a selector `X : Var Γ → Bool` that chooses a set of locally maximal variables, it recursively constructs the functoriality context `Γ ↑ X` together with two substitutions back to `Γ`:

- `in⁻`, which chooses source copies;
- `in⁺`, which chooses target copies.

When the newest variable is not selected, functoriality keeps a single copy of that variable and transports its type along the recursive inclusion:
` (Γ, x : A) ↑ X' := (Γ ↑ X, x : A[in⁻_Γ])`
` in⁻_{(Γ,x:A),X'} := ⟨in⁻_{Γ,X}, x ↦ x⟩`
` in⁺_{(Γ,x:A),X'} := ⟨in⁺_{Γ,X}, x ↦ x⟩,`
where `X = X' ∩ Var(Γ)`. When it is selected, functoriality replaces it by a source copy, a target copy, and a comparison edge between them:
` (Γ, x : A) ↑ X' := (Γ ↑ X, x⁻ : A[in⁻_Γ], x⁺ : A[in⁻_Γ], x̃ : x⁻ →_{A[in⁻_Γ]} x⁺) `
` in⁻_{(Γ,x:A),X'} := ⟨in⁻_{Γ,X}, x ↦ x⁻⟩ `
` in⁺_{(Γ,x:A),X'} := ⟨in⁺_{Γ,X}, x ↦ x⁺⟩ `
The local maximality condition ensures that this split is compatible with dependency: it means that for any variable `x:A`, the type `A` does not depend on any of the selected variables, which in turn guarantees that `A[in⁻_Γ] ≡ A[in⁺_Γ]`.

This file develops the basic selector and context machinery used later:

- Locally maximal selectors and their restriction lemmas
- The recursive definitions of `_↑_`, `in⁻`, and `in⁺`
- Agreement lemmas for types, terms, and variables independent of the selected variables
- The extension lemma `target-not-selected`, which is used repeatedly in `1f`

```agda
module 1e-FunctorialityContexts where

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; trans ; sym ; cong ; cong₂ ; subst)
open import Data.Bool.Base using (Bool; true; false; _∨_; _∧_; not)
open import Data.Nat.Base using (_≡ᵇ_)
open import 0a-Logic
open import 1a-preCaTT
  hiding (lookup-wkSub; lookup-idS; ∃-var-point-false; ∃-var-all-false)
open import 1b-Dep
open import 1c-Pasting
```

## Locally Maximal Variables

Only locally maximal variables may be selected. This is the exact condition that makes splitting stable under the dependency discipline of CaTT.

```agda
is-local-max : {Γ : Ctx} → Var Γ → Bool
is-local-max {Γ} x = ∀-var Γ (λ y → not (depends-on-var-ty x (var-to-type y)))

all-local-max : {Γ : Ctx} → (Var Γ → Bool) → Bool
all-local-max {Γ} X = ∀-var Γ (λ x → not (X x) ∨ is-local-max x)

-- A variable has maximal dimension when it reaches the ambient context
-- dimension.
is-max-dim : {Γ : Ctx} → Var Γ → Bool
is-max-dim {Γ} x = dim-var x ≡ᵇ dim-ctx Γ

all-max-dim : {Γ : Ctx} → (Var Γ → Bool) → Bool
all-max-dim {Γ} X = ∀-var Γ (λ x → not (X x) ∨ is-max-dim x)
```

## Auxiliary Lemmas

These lemmas explain how local maximality behaves when we pass to the tail of a context and when we analyze the type of the newest declaration.

```agda
-- If `vs x` is locally maximal after extension, then `x` was already locally maximal before.
is-local-max-vs :
  {Γ : Ctx} {A : Ty Γ} {x : Var Γ}
  → is-local-max {Γ = Γ , A} (vs x) ≡ true
  → is-local-max x ≡ true
is-local-max-vs {Γ} {A} {x} lm =
  ∀-var-map-true
    {P = λ y → not (depends-on-var-ty (vs x) (var-to-type (vs y)))}
    {Q = λ y → not (depends-on-var-ty x (var-to-type y))}
    step
    (∧-trueʳ lm)
  where
    step : (y : Var Γ)
      → not (depends-on-var-ty (vs x) (var-to-type (vs y))) ≡ true
      → not (depends-on-var-ty x (var-to-type y)) ≡ true
    step y p = false→not-true
      (depends-on-var-ty-vs-wk-false {A0 = A} x (var-to-type y) (not-true→false p))

-- Local maximality of `vs x` also says that `x` does not occur in the new type `A`.
is-local-max-vs-vz :
  {Γ : Ctx} {A : Ty Γ} (x : Var Γ)
  → is-local-max {Γ = Γ , A} (vs x) ≡ true
  → depends-on-var-ty x A ≡ false
is-local-max-vs-vz {Γ} {A} x lm =
  depends-on-var-ty-vs-wk-false {A0 = A} x A (not-true→false (∧-trueˡ lm))

-- Drop the newest variable from a selector.
dropLast : {Γ : Ctx} {A : Ty Γ} → (Var (Γ , A) → Bool) → Var Γ → Bool
dropLast X x = X (vs x)

-- Local maximality is preserved when we restrict a selector from `Γ , A` back to `Γ`.
local-max-restrict :
  {Γ : Ctx} {A : Ty Γ}
  → (X : Var (Γ , A) → Bool)
  → all-local-max X ≡ true
  → all-local-max (dropLast X) ≡ true
local-max-restrict {Γ} {A} X lm =
  ∀-var-map-true
    {P = λ x → not (dropLast X x) ∨ is-local-max (vs x)}
    {Q = λ x → not (dropLast X x) ∨ is-local-max x}
    step
    (∧-trueʳ lm)
  where
    step : (x : Var Γ)
      → (not (X (vs x)) ∨ is-local-max (vs x)) ≡ true
      → (not (X (vs x)) ∨ is-local-max x) ≡ true
    step x p with X (vs x)
    ... | false = refl
    ... | true = ∨-true-introʳ (is-local-max-vs {A = A} {x = x} p)

-- Drop the newest two variables, used for pasting extensions with `y` and `f`.
dropLast2 :
  {Γ : Ctx} {A : Ty Γ} {B : Ty (Γ , A)}
  → (Var ((Γ , A) , B) → Bool) → Var Γ → Bool
dropLast2 X x = X (vs (vs x))

-- The two-step version of `local-max-restrict`.
local-max-restrict2 :
  {Γ : Ctx} {A : Ty Γ} {B : Ty (Γ , A)}
  → (X : Var ((Γ , A) , B) → Bool)
  → all-local-max X ≡ true
  → all-local-max {Γ = Γ} (dropLast2 X) ≡ true
local-max-restrict2 {Γ} {A} {B} X lm =
  local-max-restrict
    {Γ = Γ} {A = A}
    (dropLast X)
    (local-max-restrict {Γ = Γ , A} {A = B} X lm)

-- If a selector is locally maximal, the newest type cannot depend on any selected old variable.
local-max-type-indep :
  {Γ : Ctx} {A : Ty Γ}
  → (X : Var (Γ , A) → Bool)
  → all-local-max X ≡ true
  → ∃-var Γ (λ x → X (vs x) ∧ depends-on-var-ty x A) ≡ false
local-max-type-indep {Γ} {A} X lm = ∃-var-all-false step
  where
    lm-tail : ∀-var Γ (λ x → not (X (vs x)) ∨ is-local-max (vs x)) ≡ true
    lm-tail = ∧-trueʳ lm

    step : (x : Var Γ) → (X (vs x) ∧ depends-on-var-ty x A) ≡ false
    step x with X (vs x) in eqX
    ... | false = refl
    ... | true =
      ∧-false-introʳ
        (is-local-max-vs-vz {A = A} x
          (∨-trueʳ-from-falseˡ
            (true→not-false eqX)
            (∀-var-elim
              {P = λ z → not (X (vs z)) ∨ is-local-max (vs z)}
              lm-tail x)))
```

## Split Edge Type

If the newest variable is selected, functoriality introduces a comparison edge between the source and target copies. This is its type.

```agda
split-edge-ty : ∀ {Γ} (A : Ty Γ) → Ty ((Γ , A) , wkTy A)
split-edge-ty A = [ wkTy (wkTy A) ] var (vs vz) ⇒ var vz
```

## Functoriality Context, Inclusions, and Agreement

The mutual block below is the actual functoriality construction for contexts. The key point is that the branch on `X vz` happens only here, once per declaration.
Everything later that reasons about functoriality contexts should reduce back to
these definitions, rather than branching on selectors again by hand.

```agda
{-# TERMINATING #-}
mutual
  -- One-step context construction. The split branch creates source, target, and comparison edge for the selected newest variable.
  ↑-step : ∀ {Γ} (A : Ty Γ) (b : Bool) (X0 : Var Γ → Bool) → Ctx
  ↑-step {Γ} A false X0 = (Γ ↑ X0) , (A [ in⁻ Γ X0 ]T)
  ↑-step {Γ} A true X0 = (((Γ ↑ X0) , A') , wkTy A') , split-edge-ty A'
    where
      A' : Ty (Γ ↑ X0)
      A' = A [ in⁻ Γ X0 ]T

  _↑_ : (Γ : Ctx) → (Var Γ → Bool) → Ctx
  ∅ ↑ X = ∅
  (Γ , A) ↑ X = ↑-step A (X vz) (dropLast X)

  -- Negative inclusion picks the source copy in every split branch.
  in⁻-step : ∀ {Γ} (A : Ty Γ) (b : Bool) (X0 : Var Γ → Bool)
    → Sub (↑-step A b X0) (Γ , A)
  in⁻-step {Γ} A false X0 = ⟨ wkSub (in⁻ Γ X0) , var vz ⟩
  in⁻-step {Γ} A true X0 =
    ⟨ wkSub (wkSub (wkSub (in⁻ Γ X0))) , var (vs (vs vz)) ⟩

  in⁻ : (Γ : Ctx) → (X : Var Γ → Bool) → Sub (Γ ↑ X) Γ
  in⁻ ∅ X = ∅S
  in⁻ (Γ , A) X = in⁻-step A (X vz) (dropLast X)

  -- Positive inclusion picks the target copy instead. This branch depends on local maximality, because only then is the target well behaved.
  in⁺-step : ∀ {Γ} (A : Ty Γ) (b : Bool) (X0 : Var Γ → Bool)
    → all-local-max X0 ≡ true
    → Sub (↑-step A b X0) (Γ , A)
  in⁺-step {Γ} A false X0 lm' = ⟨ wkSub (in⁺ Γ X0 lm') , var vz ⟩
  in⁺-step {Γ} A true X0 lm' =
    ⟨ wkSub (wkSub (wkSub (in⁺ Γ X0 lm'))) , var (vs vz) ⟩

  in⁺ : (Γ : Ctx) → (X : Var Γ → Bool)
    → all-local-max X ≡ true → Sub (Γ ↑ X) Γ
  in⁺ ∅ X lm = ∅S
  in⁺ (Γ , A) X lm = in⁺-step A (X vz) (dropLast X) (local-max-restrict X lm)

  -- Agreement is reduced to the variable case; the type and term statements are just the standard substitution congruence consequences of that fact.
  agree-ty : (Γ : Ctx) → (X : Var Γ → Bool) → (lm : all-local-max X ≡ true)
    → (A : Ty Γ) → depends-on-X-ty X A ≡ false
    → A [ in⁻ Γ X ]T ≡ A [ in⁺ Γ X lm ]T
  agree-ty Γ X lm A indep =
    sub-agree-ty A (in⁻ Γ X) (in⁺ Γ X lm)
      (λ x dx → agree-var Γ X lm x (indep-outside X A indep x dx))

  agree-tm : (Γ : Ctx) → (X : Var Γ → Bool) → (lm : all-local-max X ≡ true)
    → (t : Tm Γ) → depends-on-X-tm X t ≡ false
    → t [ in⁻ Γ X ]t ≡ t [ in⁺ Γ X lm ]t
  agree-tm Γ X lm t indep =
    sub-agree-tm t (in⁻ Γ X) (in⁺ Γ X lm)
      (λ x dx → agree-var Γ X lm x (indep-outside-tm X t indep x dx))

  -- For the newest variable, agreement only exists in the unsplit branch.
  agree-var-vz-step : ∀ {Γ} (A : Ty Γ) (b : Bool) (X0 : Var Γ → Bool)
    (lm' : all-local-max X0 ≡ true)
    → b ≡ false
    → (var vz) [ in⁻-step A b X0 ]t ≡ (var vz) [ in⁺-step A b X0 lm' ]t
  agree-var-vz-step A false X0 lm' p = refl
  agree-var-vz-step A true X0 lm' ()

  -- For older variables, agreement comes from the recursive context-level construction.
  agree-var-vs-step : ∀ {Γ} (A : Ty Γ) (b : Bool) (X0 : Var Γ → Bool)
    (lm' : all-local-max X0 ≡ true)
    (y : Var Γ)
    → X0 y ≡ false
    → (var (vs y)) [ in⁻-step A b X0 ]t ≡ (var (vs y)) [ in⁺-step A b X0 lm' ]t
  agree-var-vs-step {Γ} A false X0 lm' y px =
    trans (lookup-wkSub y (in⁻ Γ X0))
      (trans (cong wkTm ih)
        (sym (lookup-wkSub y (in⁺ Γ X0 lm'))))
    where ih = agree-var Γ X0 lm' y px
  agree-var-vs-step {Γ} A true X0 lm' y px =
    trans (lookup-wkSub y (wkSub (wkSub (in⁻ Γ X0))))
      (trans (cong wkTm
        (trans (lookup-wkSub y (wkSub (in⁻ Γ X0)))
          (cong wkTm
            (trans (lookup-wkSub y (in⁻ Γ X0))
              (cong wkTm ih)))))
        (sym
          (trans (lookup-wkSub y (wkSub (wkSub (in⁺ Γ X0 lm'))))
            (cong wkTm
              (trans (lookup-wkSub y (wkSub (in⁺ Γ X0 lm')))
                (cong wkTm
                  (lookup-wkSub y (in⁺ Γ X0 lm'))))))))
    where ih = agree-var Γ X0 lm' y px

  agree-var : (Γ : Ctx) → (X : Var Γ → Bool) → (lm : all-local-max X ≡ true)
    → (x : Var Γ) → X x ≡ false
    → (var x) [ in⁻ Γ X ]t ≡ (var x) [ in⁺ Γ X lm ]t
  agree-var ∅ X lm () px
  agree-var (Γ , A) X lm vz px =
    agree-var-vz-step A (X vz) (dropLast X) (local-max-restrict X lm) px
  agree-var (Γ , A) X lm (vs y) px =
    agree-var-vs-step A (X vz) (dropLast X) (local-max-restrict X lm) y px
```

## Pasting Extension Helper

The next file studies a pasting extension `ext-ctx xps`, whose newest variables are the comparison edge `f` and its target `y`. Observe that the selecter can never choose the variable `y`, as it is not locally maximal: the type of `f` depends on `y`. The lemma `target-not-selected` packages exactly this observation.

```agda
edge-dep-on-target :
  ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
  → depends-on-var-ty vz (hom-type-ext xps) ≡ true
edge-dep-on-target {Γ} xps =
  ∨-true-introʳ
    {b = depends-on-var-ty {Γ = Γ , varps-to-type xps} vz (wkTy (varps-to-type xps))}
    {c = depends-on-var-tm {Γ = Γ , varps-to-type xps} vz (var (vs (varps-to-var xps)))
       ∨ depends-on-var-tm {Γ = Γ , varps-to-type xps} vz (var vz)}
    (∨-true-introʳ
      {b = depends-on-var-tm {Γ = Γ , varps-to-type xps} vz (var (vs (varps-to-var xps)))}
      {c = depends-on-var-tm {Γ = Γ , varps-to-type xps} vz (var vz)}
      refl)

-- The target endpoint of the new edge is therefore forbidden by local
-- maximality.
target-not-selected :
  ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
  → (X : Var (ext-ctx xps) → Bool)
  → all-local-max X ≡ true
  → X (vs vz) ≡ false
target-not-selected xps X lm =
  ∧-falseˡ-from-trueʳ
    (∃-var-point-false
      {P = λ x → X (vs x) ∧ depends-on-var-ty x (hom-type-ext xps)}
      vz
      (local-max-type-indep X lm))
    (edge-dep-on-target xps)

-- Restrict a selector on `ext-ctx xps` back to the base context.
ext-base-selector :
  ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
  → (Var (ext-ctx xps) → Bool) → Var Γ → Bool
ext-base-selector {Γ} xps =
  dropLast2 {Γ = Γ} {A = varps-to-type xps} {B = hom-type-ext xps}

-- Local maximality survives this two-variable restriction back to the base.
ext-base-selector-local-max :
  ∀ {Γ} {Γps : CtxPs Γ}
  (xps : VarPs Γ Γps)
  (X : Var (ext-ctx xps) → Bool)
  (lm : all-local-max X ≡ true)
  → all-local-max (ext-base-selector xps X) ≡ true
ext-base-selector-local-max xps X lm = local-max-restrict2 X lm

-- The source endpoint of the new edge is not locally maximal either.
edge-dep-on-source :
  ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
  → depends-on-var-ty (vs (varps-to-var xps)) (hom-type-ext xps) ≡ true
edge-dep-on-source {Γ} xps =
  ∨-true-introʳ
    {b = depends-on-var-ty {Γ = Γ , varps-to-type xps}
           (vs (varps-to-var xps)) (wkTy (varps-to-type xps))}
    {c = depends-on-var-tm {Γ = Γ , varps-to-type xps}
           (vs (varps-to-var xps)) (var (vs (varps-to-var xps)))
       ∨ depends-on-var-tm {Γ = Γ , varps-to-type xps}
           (vs (varps-to-var xps)) (var vz)}
    (∨-true-introˡ
      {b = depends-on-var-tm {Γ = Γ , varps-to-type xps}
             (vs (varps-to-var xps)) (var (vs (varps-to-var xps)))}
      {c = depends-on-var-tm {Γ = Γ , varps-to-type xps}
             (vs (varps-to-var xps)) (var vz)}
      (dep-var-refl {Γ = Γ , varps-to-type xps} (vs (varps-to-var xps))))

-- Therefore the old dangling variable also cannot be selected in the extension.
dangling-not-selected :
  ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
  → (X : Var (ext-ctx xps) → Bool)
  → all-local-max X ≡ true
  → X (vs (vs (varps-to-var xps))) ≡ false
dangling-not-selected xps X lm =
  ∧-falseˡ-from-trueʳ
    (∃-var-point-false
      {P = λ x → X (vs x) ∧ depends-on-var-ty x (hom-type-ext xps)}
      (vs (varps-to-var xps))
      (local-max-type-indep X lm))
    (edge-dep-on-source xps)

-- Evaluating the restricted selector on the old dangling variable just shifts indices twice.
ext-base-selector-dangling :
  ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
  → (X : Var (ext-ctx xps) → Bool)
  → ext-base-selector xps X (varps-to-var xps)
    ≡ X (vs (vs (varps-to-var xps)))
ext-base-selector-dangling xps X = refl

-- Combining the two previous lemmas yields the non-selection fact needed in `1f`.
ext-base-selector-dangling-not-selected :
  ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
  → (X : Var (ext-ctx xps) → Bool)
  → (lm : all-local-max X ≡ true)
  → ext-base-selector xps X (varps-to-var xps) ≡ false
ext-base-selector-dangling-not-selected xps X lm =
  trans (ext-base-selector-dangling xps X)
    (dangling-not-selected xps X lm)

-- Congruence for a one-step context extension.
snocCtx-cong :
  ∀ {Γ Γ' : Ctx} (eΓ : Γ ≡ Γ') {A : Ty Γ} {A' : Ty Γ'}
  → subst Ty eΓ A ≡ A'
  → (Γ , A) ≡ (Γ' , A')
snocCtx-cong refl refl = refl

-- Congruence for the split branch of functoriality.
splitCtx-cong :
  ∀ {Γ Γ' : Ctx} (eΓ : Γ ≡ Γ') {A : Ty Γ} {A' : Ty Γ'}
  → subst Ty eΓ A ≡ A'
  → ((((Γ , A) , wkTy A) , split-edge-ty A))
    ≡ ((((Γ' , A') , wkTy A') , split-edge-ty A'))
splitCtx-cong refl refl = refl

-- Substituting along equal substitutions preserves substituted types.
subst-[]T :
  ∀ {Γ Δ Δ'} {A : Ty Γ} (e : Δ ≡ Δ') {σ : Sub Δ Γ} {τ : Sub Δ' Γ}
  → subst (λ Z → Sub Z Γ) e σ ≡ τ
  → subst Ty e (A [ σ ]T) ≡ A [ τ ]T
subst-[]T refl refl = refl

-- The term-level analogue of `subst-[]T`.
subst-[]t :
  ∀ {Γ Δ Δ'} {t : Tm Γ} (e : Δ ≡ Δ') {σ : Sub Δ Γ} {τ : Sub Δ' Γ}
  → subst (λ Z → Sub Z Γ) e σ ≡ τ
  → subst Tm e (t [ σ ]t) ≡ t [ τ ]t
subst-[]t refl refl = refl

-- Transporting an unsplit inclusion along context equality keeps the same newest variable.
subst-snocSub-vz :
  ∀ {Γ Δ Δ' : Ctx} (eΔ : Δ ≡ Δ') {A : Ty Γ} {B : Ty Δ} {B' : Ty Δ'}
  → (eB : subst Ty eΔ B ≡ B')
  → {σ : Sub Δ Γ} {τ : Sub Δ' Γ}
  → subst (λ Z → Sub Z Γ) eΔ σ ≡ τ
  → subst (λ Z → Sub Z (Γ , A)) (snocCtx-cong eΔ eB) (⟨ wkSub σ , var vz ⟩)
    ≡ ⟨ wkSub τ , var vz ⟩
subst-snocSub-vz refl refl refl = refl

-- The corresponding transport fact for the split inclusion.
subst-splitSub-vs-vs-vz :
  ∀ {Γ Δ Δ' : Ctx} (eΔ : Δ ≡ Δ') {A : Ty Γ} {B : Ty Δ} {B' : Ty Δ'}
  → (eB : subst Ty eΔ B ≡ B')
  → {σ : Sub Δ Γ} {τ : Sub Δ' Γ}
  → subst (λ Z → Sub Z Γ) eΔ σ ≡ τ
  → subst (λ Z → Sub Z (Γ , A)) (splitCtx-cong eΔ eB)
      (⟨ wkSub (wkSub (wkSub σ)) , var (vs (vs vz)) ⟩)
    ≡ ⟨ wkSub (wkSub (wkSub τ)) , var (vs (vs vz)) ⟩
subst-splitSub-vs-vs-vz refl refl refl = refl

-- The positive split branch uses `var (vs vz)` instead of `var (vs (vs vz))`.
subst-splitSub-vs-vz :
  ∀ {Γ Δ Δ' : Ctx} (eΔ : Δ ≡ Δ') {A : Ty Γ} {B : Ty Δ} {B' : Ty Δ'}
  → (eB : subst Ty eΔ B ≡ B')
  → {σ : Sub Δ Γ} {τ : Sub Δ' Γ}
  → subst (λ Z → Sub Z Γ) eΔ σ ≡ τ
  → subst (λ Z → Sub Z (Γ , A)) (splitCtx-cong eΔ eB)
      (⟨ wkSub (wkSub (wkSub σ)) , var (vs vz) ⟩)
    ≡ ⟨ wkSub (wkSub (wkSub τ)) , var (vs vz) ⟩
subst-splitSub-vs-vz refl refl refl = refl

-- Universal quantification over variables respects pointwise equality of predicates.
∀-var-cong :
  ∀ {Γ} {P Q : Var Γ → Bool}
  → ((x : Var Γ) → P x ≡ Q x)
  → ∀-var Γ P ≡ ∀-var Γ Q
∀-var-cong {Γ = ∅} h = refl
∀-var-cong {Γ = Γ , A} {P} {Q} h
  rewrite h vz
        | ∀-var-cong {Γ = Γ} {P = λ x → P (vs x)} {Q = λ x → Q (vs x)}
            (λ x → h (vs x))
  = refl

-- Hence local maximality itself is invariant under pointwise-equal selectors.
abstract
  all-local-max-cong :
    ∀ {Γ} (X Y : Var Γ → Bool)
    → ((x : Var Γ) → X x ≡ Y x)
    → all-local-max X ≡ all-local-max Y
  all-local-max-cong X Y h =
    ∀-var-cong (λ x → cong (λ b → not b ∨ is-local-max x) (h x))

  all-max-dim-cong :
    ∀ {Γ} (X Y : Var Γ → Bool)
    → ((x : Var Γ) → X x ≡ Y x)
    → all-max-dim X ≡ all-max-dim Y
  all-max-dim-cong X Y h =
    ∀-var-cong (λ x → cong (λ b → not b ∨ is-max-dim x) (h x))

mutual
  -- Branch-agnostic congruence for `↑-step`: dispatches to `snocCtx-cong`
  -- or `splitCtx-cong` according to the branch flag.
  ↑-step-cong :
    ∀ {Γ} (A : Ty Γ) (b : Bool) (X0 Y0 : Var Γ → Bool)
    → (eΓ : Γ ↑ X0 ≡ Γ ↑ Y0)
    → subst Ty eΓ (A [ in⁻ Γ X0 ]T) ≡ A [ in⁻ Γ Y0 ]T
    → ↑-step A b X0 ≡ ↑-step A b Y0
  ↑-step-cong A false X0 Y0 eΓ eA = snocCtx-cong eΓ eA
  ↑-step-cong A true X0 Y0 eΓ eA = splitCtx-cong eΓ eA

  -- And the corresponding congruence for `in⁻-step`.
  in⁻-step-cong :
    ∀ {Γ} (A : Ty Γ) (b : Bool) (X0 Y0 : Var Γ → Bool)
    → (eΓ : Γ ↑ X0 ≡ Γ ↑ Y0)
    → (eA : subst Ty eΓ (A [ in⁻ Γ X0 ]T) ≡ A [ in⁻ Γ Y0 ]T)
    → (eσ : subst (λ Δ → Sub Δ Γ) eΓ (in⁻ Γ X0) ≡ in⁻ Γ Y0)
    → subst (λ Z → Sub Z (Γ , A))
        (↑-step-cong A b X0 Y0 eΓ eA)
        (in⁻-step A b X0)
      ≡ in⁻-step A b Y0
  in⁻-step-cong A false X0 Y0 eΓ eA eσ = subst-snocSub-vz eΓ eA eσ
  in⁻-step-cong A true X0 Y0 eΓ eA eσ = subst-splitSub-vs-vs-vz eΓ eA eσ

  -- The positive inclusion satisfies the analogous transport law, but now
  -- the recursive inclusions also carry local-maximality proofs.
  in⁺-step-cong :
    ∀ {Γ} (A : Ty Γ) (b : Bool) (X0 Y0 : Var Γ → Bool)
    → (lmX : all-local-max X0 ≡ true)
    → (lmY : all-local-max Y0 ≡ true)
    → (eΓ : Γ ↑ X0 ≡ Γ ↑ Y0)
    → (eA : subst Ty eΓ (A [ in⁻ Γ X0 ]T) ≡ A [ in⁻ Γ Y0 ]T)
    → (eσ : subst (λ Δ → Sub Δ Γ) eΓ (in⁺ Γ X0 lmX) ≡ in⁺ Γ Y0 lmY)
    → subst (λ Z → Sub Z (Γ , A))
        (↑-step-cong A b X0 Y0 eΓ eA)
        (in⁺-step A b X0 lmX)
      ≡ in⁺-step A b Y0 lmY
  in⁺-step-cong A false X0 Y0 lmX lmY eΓ eA eσ = subst-snocSub-vz eΓ eA eσ
  in⁺-step-cong A true X0 Y0 lmX lmY eΓ eA eσ = subst-splitSub-vs-vz eΓ eA eσ

  -- Pointwise equal selectors build definitionally equal functoriality contexts.
  selector-cong-up :
    (Δ : Ctx) → (X Y : Var Δ → Bool)
    → ((x : Var Δ) → X x ≡ Y x)
    → Δ ↑ X ≡ Δ ↑ Y
  selector-cong-up ∅ X Y h = refl
  selector-cong-up (Γ , A) X Y h with X vz | Y vz | h vz
  ... | b | .b | refl = ↑-step-cong A b (dropLast X) (dropLast Y) eΓ (subst-[]T eΓ eσ)
    where
      eΓ = selector-cong-up Γ (dropLast X) (dropLast Y) (λ x → h (vs x))
      eσ = selector-cong-in⁻ Γ (dropLast X) (dropLast Y) (λ x → h (vs x))

  -- And their negative inclusions agree after transport along that context equality.
  selector-cong-in⁻ :
    (Γ : Ctx) → (X Y : Var Γ → Bool)
    → (h : (x : Var Γ) → X x ≡ Y x)
    → subst (λ Δ → Sub Δ Γ) (selector-cong-up Γ X Y h) (in⁻ Γ X) ≡ in⁻ Γ Y
  selector-cong-in⁻ ∅ X Y h = refl
  selector-cong-in⁻ (Γ , A) X Y h with X vz | Y vz | h vz
  ... | b | .b | refl = in⁻-step-cong A b (dropLast X) (dropLast Y) eΓ eA eσ
    where
      eΓ = selector-cong-up Γ (dropLast X) (dropLast Y) (λ x → h (vs x))
      eσ = selector-cong-in⁻ Γ (dropLast X) (dropLast Y) (λ x → h (vs x))
      eA = subst-[]T eΓ eσ

  -- And likewise for their positive inclusions, provided we supply the
  -- local-maximality proofs on both sides.
  selector-cong-in⁺ :
    (Γ : Ctx) → (X Y : Var Γ → Bool)
    → (h : (x : Var Γ) → X x ≡ Y x)
    → (lmX : all-local-max X ≡ true)
    → (lmY : all-local-max Y ≡ true)
    → subst (λ Δ → Sub Δ Γ) (selector-cong-up Γ X Y h) (in⁺ Γ X lmX) ≡ in⁺ Γ Y lmY
  selector-cong-in⁺ ∅ X Y h lmX lmY = refl
  selector-cong-in⁺ (Γ , A) X Y h lmX lmY
    with X vz | Y vz | h vz
       | local-max-restrict X lmX
       | local-max-restrict Y lmY
  ... | b | .b | refl | lmX' | lmY' =
    in⁺-step-cong A b (dropLast X) (dropLast Y) lmX' lmY' eΓ eA eσ
    where
      h0 : (x : Var Γ) → dropLast X x ≡ dropLast Y x
      h0 x = h (vs x)

      eΓ : Γ ↑ dropLast X ≡ Γ ↑ dropLast Y
      eΓ = selector-cong-up Γ (dropLast X) (dropLast Y) h0

      eσ⁻ : subst (λ Δ → Sub Δ Γ) eΓ (in⁻ Γ (dropLast X)) ≡ in⁻ Γ (dropLast Y)
      eσ⁻ = selector-cong-in⁻ Γ (dropLast X) (dropLast Y) h0

      eA : subst Ty eΓ (A [ in⁻ Γ (dropLast X) ]T) ≡ A [ in⁻ Γ (dropLast Y) ]T
      eA = subst-[]T eΓ eσ⁻

      eσ : subst (λ Δ → Sub Δ Γ) eΓ (in⁺ Γ (dropLast X) lmX') ≡ in⁺ Γ (dropLast Y) lmY'
      eσ = selector-cong-in⁺ Γ (dropLast X) (dropLast Y) h0 lmX' lmY'

-- Stable names for the two one-step branch contexts of functoriality.
unsplit-branch-ctx :
  ∀ {Γ} (A : Ty Γ) (X : Var (Γ , A) → Bool) → Ctx
unsplit-branch-ctx {Γ} A X =
  (Γ ↑ dropLast X) , (A [ in⁻ Γ (dropLast X) ]T)

-- The split branch adds source copy, target copy, and comparison edge.
split-branch-ctx :
  ∀ {Γ} (A : Ty Γ) (X : Var (Γ , A) → Bool) → Ctx
split-branch-ctx {Γ} A X =
  (((Γ ↑ dropLast X) , A') , wkTy A') , split-edge-ty A'
  where
    A' : Ty (Γ ↑ dropLast X)
    A' = A [ in⁻ Γ (dropLast X) ]T

-- If the newest variable is unselected, `_↑_` really is the unsplit branch.
functoriality-ctx-unsplit :
  ∀ {Γ} (A : Ty Γ) (X : Var (Γ , A) → Bool)
  → X vz ≡ false
  → ((Γ , A) ↑ X) ≡ unsplit-branch-ctx A X
functoriality-ctx-unsplit {Γ} A X p with X vz
... | false = refl
... | true with p
... | ()

-- If it is selected, `_↑_` really is the split branch.
functoriality-ctx-split :
  ∀ {Γ} (A : Ty Γ) (X : Var (Γ , A) → Bool)
  → X vz ≡ true
  → ((Γ , A) ↑ X) ≡ split-branch-ctx A X
functoriality-ctx-split {Γ} A X p with X vz
... | true = refl
... | false with p
... | ()

-- In the unsplit branch, the newest variable maps to itself under `in⁻`.
lookup-vz-in⁻-unsplit :
  ∀ {Γ} (A : Ty Γ) (X : Var (Γ , A) → Bool)
  → (p : X vz ≡ false)
  → subst Tm (functoriality-ctx-unsplit A X p)
      (var vz [ in⁻ (Γ , A) X ]t)
    ≡ var vz
lookup-vz-in⁻-unsplit {Γ} A X p with X vz
... | false = refl
... | true with p
... | ()
```

