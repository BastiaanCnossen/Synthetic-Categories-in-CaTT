# 1f-FunctorialityPasting: Functoriality Preserves Pasting Contexts

This module is the pasting-specific part of pre-syntax functoriality. The previous file `1e-FunctorialityContexts` constructs, for a context `Γ` and a selector `X : Var Γ → Bool`, the functoriality context `Γ ↑ X` together with the substitutions `in⁻ : Γ ↑ X → Γ` and `in⁺ : Γ ↑ X → Γ`. Here we show that if `Γ` is presented as a pasting context, then its functorial image is again a pasting context.

The key design choice is that the recursive proof does not work directly with a raw boolean selector. Instead it works with a structured selector `PsSel Γps` which remembers, for every pasting extension, whether we are in the split or unsplit case. This keeps the recursion constructor-headed and avoids repeatedly asking Agda to recover branch information from a bare function `Var Γ → Bool`.

The mutual proof establishes four facts simultaneously:

- `func-pasting`: functoriality sends pasting contexts to pasting contexts
- `func-dangling`: each dangling variable is transported to a dangling variable in the image pasting context
- `func-dangling-type`: the transported dangling type is exactly the old one substituted along `in⁻`
- `func-dangling-var`: the transported variable term is also carried by `in⁻`

At an extension `ps-ext xps` there are two geometric branches. In the unsplit branch the new edge `f` is left untouched, so the image context aligns with the ordinary extension of the recursively transported dangling variable `d`. In the split branch the new edge is selected, local maximality forces the new target `y` not to be selected, and the image context aligns with the extension built
from `varps-f d`. The central block of the file proves the corresponding alignment lemmas and then extracts the transported witnesses for `f`, `y`, and the weakened older variables.

The final section translates back to the raw selector language. This is what later functoriality constructions need when they state naturality of terms, types, substitutions, and coherences using an ordinary selector `X : Var Γ → Bool`.

```agda
module 1f-FunctorialityPasting where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst)
open import Data.Bool.Base using (Bool; true; false; not; _∨_; _∧_)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (<-trans)
open import 0a-Logic using
  ( ∧-falseˡ-from-trueʳ
  ; ∨-true-introˡ
  ; ∨-true-introʳ
  ; ∨3-falseˡ
  ; ∨3-falseᵐ
  ; ∨3-falseʳ
  ; false→not-true
  ; true≠false
  )
open import 1b-Dep using
  ( depends-on-var-ty
  ; depends-on-var-tm
  ; depends-on-var-sub-at
  ; depends-on-var-sub
  ; depends-on-var-sub-at-lookup
  ; depends-on-var-ty-vz-wk-false
  ; dep-var-refl
  ; hom-cong3
  )
open import 1a-preCaTT
open import 1c-Pasting
open import 1e-FunctorialityContexts public
```

## General Helpers

These first lemmas are just proof-combinators used to keep later transport
arguments readable. They are not specific to functoriality of pasting
contexts, but they are small enough that keeping them local still makes the
main body easier to follow.

```agda
-- Strict inequalities are preserved when both endpoints are transported along equalities.
<-cong :
  ∀ {m n m' n' : ℕ}
  → m ≡ m' → n ≡ n' → m < n → m' < n'
<-cong refl refl lt = lt

abstract
  -- Equality proofs into `false` are unique, so branch evidence can be normalized away.
  bool-false-eq-unique :
    ∀ {b : Bool} (p q : b ≡ false) → p ≡ q
  bool-false-eq-unique {false} refl refl = refl
  bool-false-eq-unique {true} () q
```

## Structured Selectors

The natural-language proof starts by replacing a raw selector `X : Var Γ → Bool`
with a constructor-headed selector object. For an extension we do not want to
re-discover, over and over, whether the newest variable is split or unsplit;
that information is now stored directly in the shape of `PsSel`.

```agda

mutual
  -- A structured selector remembers, at each extension, whether we are in the
  -- split or unsplit branch and stores the required local-maximality evidence.
  data PsSel : ∀ {Γ} → CtxPs Γ → Set where
    pssel-ob-unsplit : PsSel ps-ob
    pssel-ob-split   : PsSel ps-ob
    unsplitSel :
      ∀ {Γ} {Γps : CtxPs Γ} {xps : VarPs Γ Γps}
      → (s0 : PsSel Γps)
      → (lm0 : all-local-max (eval-step-unsplit {xps = xps} s0) ≡ true)
      → eval-ps-sel s0 (varps-to-var xps) ≡ false
      → PsSel (ps-ext xps)
    splitSel :
      ∀ {Γ} {Γps : CtxPs Γ} {xps : VarPs Γ Γps}
      → (s0 : PsSel Γps)
      → (lm0 : all-local-max (eval-step-split {xps = xps} s0) ≡ true)
      → eval-ps-sel s0 (varps-to-var xps) ≡ false
      → PsSel (ps-ext xps)

  -- The unsplit branch leaves the newest edge `f` and target `y` unselected.
  eval-step-unsplit :
    ∀ {Γ} {Γps : CtxPs Γ} {xps : VarPs Γ Γps}
    → PsSel Γps → Var (ext-ctx xps) → Bool
  eval-step-unsplit s0 vz = false
  eval-step-unsplit s0 (vs vz) = false
  eval-step-unsplit s0 (vs (vs x)) = eval-ps-sel s0 x

  -- The split branch selects the newest edge `f`, but never the target `y`.
  eval-step-split :
    ∀ {Γ} {Γps : CtxPs Γ} {xps : VarPs Γ Γps}
    → PsSel Γps → Var (ext-ctx xps) → Bool
  eval-step-split s0 vz = true
  eval-step-split s0 (vs vz) = false
  eval-step-split s0 (vs (vs x)) = eval-ps-sel s0 x

  -- Forgetting the structure recovers the underlying raw selector.
  eval-ps-sel :
    ∀ {Γ} {Γps : CtxPs Γ}
    → PsSel Γps → Var Γ → Bool
  eval-ps-sel pssel-ob-unsplit vz = false
  eval-ps-sel pssel-ob-split vz = true
  eval-ps-sel (unsplitSel {xps = xps} s0 lm0 notSel) =
    eval-step-unsplit {xps = xps} s0
  eval-ps-sel (splitSel {xps = xps} s0 lm0 notSel) =
    eval-step-split {xps = xps} s0

abstract
  -- Every structured selector comes with its local-maximality proof.
  pssel-local-max :
    ∀ {Γ} {Γps : CtxPs Γ}
    → (s : PsSel Γps)
    → all-local-max (eval-ps-sel s) ≡ true
  pssel-local-max pssel-ob-unsplit = refl
  pssel-local-max pssel-ob-split = refl
  pssel-local-max (unsplitSel s0 lm0 notSel) = lm0
  pssel-local-max (splitSel s0 lm0 notSel) = lm0

-- On an extension, evaluation is just evaluation of the structured selector itself.
eval-ext-sel :
  ∀ {Γ} {Γps : CtxPs Γ} {xps : VarPs Γ Γps}
  → PsSel (ps-ext xps) → Var (ext-ctx xps) → Bool
eval-ext-sel = eval-ps-sel

-- The previous-stage selector is the recursive selector on the base pasting context.
prev-pssel :
  ∀ {Γ} {Γps : CtxPs Γ} {xps : VarPs Γ Γps}
  → PsSel (ps-ext xps) → PsSel Γps
prev-pssel (unsplitSel s0 lm0 notSel) = s0
prev-pssel (splitSel s0 lm0 notSel) = s0

-- Its underlying raw selector on Γ.
prev-selector :
  ∀ {Γ} {Γps : CtxPs Γ} {xps : VarPs Γ Γps}
  → PsSel (ps-ext xps) → Var Γ → Bool
prev-selector s = eval-ps-sel (prev-pssel s)

abstract
  -- Local maximality also restricts to that base selector.
  prev-selector-local-max :
    ∀ {Γ} {Γps : CtxPs Γ} {xps : VarPs Γ Γps}
    → (s : PsSel (ps-ext xps)) → all-local-max (prev-selector s) ≡ true
  prev-selector-local-max s = pssel-local-max (prev-pssel s)

  -- And the old dangling variable is never selected there.
  prev-selector-not-selected :
    ∀ {Γ} {Γps : CtxPs Γ} {xps : VarPs Γ Γps}
    → (s : PsSel (ps-ext xps)) → prev-selector s (varps-to-var xps) ≡ false
  prev-selector-not-selected (unsplitSel s0 lm0 notSel) = notSel
  prev-selector-not-selected (splitSel s0 lm0 notSel) = notSel
```

## Selector Legality

The next lemmas justify switching between the split and unsplit presentations
of a step. The key observation is that the newest edge variable `f` is always
locally maximal, so forcing it on or off does not affect the legality of the
rest of the selector.

```agda
abstract
  -- The newest edge variable in an extension is always locally maximal.
  edge-local-max :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → is-local-max {Γ = ext-ctx xps} vz ≡ true
  edge-local-max {Γ} xps =
    ∀-var-map-true step (∀-var-const-true {Γ = ext-ctx xps})
    where
      step : (y : Var (ext-ctx xps))
        → true ≡ true
        → not (depends-on-var-ty vz (var-to-type y)) ≡ true
      step vz p = false→not-true (depends-on-var-ty-vz-wk-false (hom-type-ext xps))
      step (vs y) p = false→not-true (depends-on-var-ty-vz-wk-false (var-to-type y))

  -- So a legal split selector can be viewed as a legal unsplit selector.
  split-lm→unsplit-lm :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps) (s0 : PsSel Γps)
    → all-local-max (eval-step-split {xps = xps} s0) ≡ true
    → all-local-max (eval-step-unsplit {xps = xps} s0) ≡ true
  split-lm→unsplit-lm xps s0 lm rewrite edge-local-max xps = lm

  -- And conversely, turning on the newest edge preserves legality.
  unsplit-lm→split-lm :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps) (s0 : PsSel Γps)
    → all-local-max (eval-step-unsplit {xps = xps} s0) ≡ true
    → all-local-max (eval-step-split {xps = xps} s0) ≡ true
  unsplit-lm→split-lm xps s0 lm rewrite edge-local-max xps = lm

-- Canonically coerce any selector on an extension into its unsplit view.
unsplitSel-from :
  ∀ {Γ} {Γps : CtxPs Γ} {xps : VarPs Γ Γps}
  → PsSel (ps-ext xps) → PsSel (ps-ext xps)
unsplitSel-from {xps = xps} (unsplitSel s0 lm0 notSel) =
  unsplitSel s0 lm0 notSel
unsplitSel-from {xps = xps} (splitSel s0 lm0 notSel) =
  unsplitSel s0 (split-lm→unsplit-lm xps s0 lm0) notSel

-- Canonically coerce any selector on an extension into its split view.
splitSel-from :
  ∀ {Γ} {Γps : CtxPs Γ} {xps : VarPs Γ Γps}
  → PsSel (ps-ext xps) → PsSel (ps-ext xps)
splitSel-from {xps = xps} (unsplitSel s0 lm0 notSel) =
  splitSel s0 (unsplit-lm→split-lm xps s0 lm0) notSel
splitSel-from {xps = xps} (splitSel s0 lm0 notSel) =
  splitSel s0 lm0 notSel
```

## Transport and Branch Shapes

At this point the proof follows the natural-language outline directly. Given an
extension `ps-ext xps`, recurse on the previous selector, obtain the recursive
dangling witness `d`, and then identify the new functorial context with the
appropriate standard pasting extension built from `d`. Most of the code in this
section is bookkeeping for those identifications.

```agda

-- Transport a dangling witness across an equality of ambient contexts.
transport-VarPs :
  ∀ {Γ Γ' : Ctx} (eq : Γ ≡ Γ') {Γps : CtxPs Γ}
  → VarPs Γ Γps
  → VarPs Γ' (subst CtxPs eq Γps)
transport-VarPs refl xps = xps

-- Transport commutes with taking the type of a dangling witness.
varps-to-type-transport :
  ∀ {Γ Γ' : Ctx} (eq : Γ ≡ Γ') {Γps : CtxPs Γ}
  (xps : VarPs Γ Γps)
  → varps-to-type (transport-VarPs eq xps)
    ≡ subst Ty eq (varps-to-type xps)
varps-to-type-transport refl xps = refl

-- And likewise with taking its underlying variable.
varps-to-var-transport :
  ∀ {Γ Γ' : Ctx} (eq : Γ ≡ Γ') {Γps : CtxPs Γ}
  (xps : VarPs Γ Γps)
  → varps-to-var (transport-VarPs eq xps)
    ≡ subst Var eq (varps-to-var xps)
varps-to-var-transport refl xps = refl

-- Congruence for adding one dependent type to a context.
snocCtx-cong-dep :
  ∀ {Γ} {A A' : Ty Γ} {B : Ty (Γ , A)} {B' : Ty (Γ , A')}
  → (eA : A ≡ A')
  → (eB : subst (λ X → Ty (Γ , X)) eA B ≡ B')
  → ((Γ , A) , B) ≡ ((Γ , A') , B')
snocCtx-cong-dep refl refl = refl

-- Weakening is stable under transport between equal base types.
subst-wkTy-transport :
  ∀ {Γ} {C1 C2 : Ty Γ} (e : C1 ≡ C2) (T : Ty Γ)
  → subst (λ C → Ty (Γ , C)) e (wkTy {A = C1} T)
    ≡ wkTy {A = C2} T
subst-wkTy-transport refl T = refl

-- Variables not mentioning the transported top slot are unchanged by transport.
subst-var-vs :
  ∀ {Γ} {C1 C2 : Ty Γ} (e : C1 ≡ C2) (x : Var Γ)
  → subst (λ C → Tm (Γ , C)) e (var (vs x)) ≡ var (vs x)
subst-var-vs refl x = refl

-- The newest variable is also fixed by reflexive transport.
subst-var-vz :
  ∀ {Γ} {C1 C2 : Ty Γ} (e : C1 ≡ C2)
  → subst (λ C → Tm (Γ , C)) e (var vz) ≡ var vz
subst-var-vz refl = refl

-- Hom-types transport componentwise once their base type and endpoints do.
subst-hom-ty-transport :
  ∀ {Γ} {C1 C2 : Ty Γ} (e : C1 ≡ C2)
  (base1 : Ty (Γ , C1)) (base2 : Ty (Γ , C2))
  (u1 v1 : Tm (Γ , C1)) (u2 v2 : Tm (Γ , C2))
  (e-base : subst (λ C → Ty (Γ , C)) e base1 ≡ base2)
  (e-u : subst (λ C → Tm (Γ , C)) e u1 ≡ u2)
  (e-v : subst (λ C → Tm (Γ , C)) e v1 ≡ v2)
  → subst (λ C → Ty (Γ , C)) e ([ base1 ] u1 ⇒ v1)
    ≡ [ base2 ] u2 ⇒ v2
subst-hom-ty-transport refl base1 base2 u1 v1 u2 v2 e-base e-u e-v =
  hom-cong3 e-base e-u e-v

splitCtx-cong-dep :
  ∀ {Δ} {C1 C2 : Ty Δ} {H1 : Ty (Δ , C1)} {H2 : Ty (Δ , C2)}
  → (eC : C1 ≡ C2)
  → (eH : subst (λ C → Ty (Δ , C)) eC H1 ≡ H2)
  → ((((Δ , C1) , H1) , wkTy H1) , split-edge-ty H1)
    ≡ ((((Δ , C2) , H2) , wkTy H2) , split-edge-ty H2)
splitCtx-cong-dep refl refl = refl

subst-snocCtx-cong-dep-wkTy :
  ∀ {Δ} {C1 C2 : Ty Δ} {H1 : Ty (Δ , C1)} {H2 : Ty (Δ , C2)}
  → (eC : C1 ≡ C2)
  → (eH : subst (λ C → Ty (Δ , C)) eC H1 ≡ H2)
  → subst Ty (sym (snocCtx-cong-dep eC eH)) (wkTy H2) ≡ wkTy H1
subst-snocCtx-cong-dep-wkTy refl refl = refl

subst-snocCtx-cong-dep-double-wkTy :
  ∀ {Δ} {C1 C2 : Ty Δ} {H1 : Ty (Δ , C1)} {H2 : Ty (Δ , C2)}
  → (eC : C1 ≡ C2)
  → (eH : subst (λ C → Ty (Δ , C)) eC H1 ≡ H2)
  → subst Ty (sym (snocCtx-cong-dep eC eH)) (wkTy (wkTy C2))
      ≡ wkTy (wkTy C1)
subst-snocCtx-cong-dep-double-wkTy refl refl = refl

subst-snocCtx-cong-dep-double-wkTy-any :
  ∀ {Δ} {C1 C2 : Ty Δ} {H1 : Ty (Δ , C1)} {H2 : Ty (Δ , C2)}
  → (eC : C1 ≡ C2)
  → (eH : subst (λ C → Ty (Δ , C)) eC H1 ≡ H2)
  → (T : Ty Δ)
  → subst Ty (sym (snocCtx-cong-dep eC eH)) (wkTy (wkTy T))
      ≡ wkTy (wkTy T)
subst-snocCtx-cong-dep-double-wkTy-any refl refl T = refl

subst-snocCtx-cong-dep-vz :
  ∀ {Δ} {C1 C2 : Ty Δ} {H1 : Ty (Δ , C1)} {H2 : Ty (Δ , C2)}
  → (eC : C1 ≡ C2)
  → (eH : subst (λ C → Ty (Δ , C)) eC H1 ≡ H2)
  → subst Var (sym (snocCtx-cong-dep eC eH)) vz ≡ vz
subst-snocCtx-cong-dep-vz refl refl = refl

subst-snocCtx-cong-dep-vs-vz :
  ∀ {Δ} {C1 C2 : Ty Δ} {H1 : Ty (Δ , C1)} {H2 : Ty (Δ , C2)}
  → (eC : C1 ≡ C2)
  → (eH : subst (λ C → Ty (Δ , C)) eC H1 ≡ H2)
  → subst Var (sym (snocCtx-cong-dep eC eH)) (vs vz) ≡ vs vz
subst-snocCtx-cong-dep-vs-vz refl refl = refl

subst-snocCtx-cong-dep-vs-vs :
  ∀ {Δ} {C1 C2 : Ty Δ} {H1 : Ty (Δ , C1)} {H2 : Ty (Δ , C2)}
  → (eC : C1 ≡ C2)
  → (eH : subst (λ C → Ty (Δ , C)) eC H1 ≡ H2)
  → (x : Var Δ)
  → subst Var (sym (snocCtx-cong-dep eC eH)) (vs (vs x)) ≡ vs (vs x)
subst-snocCtx-cong-dep-vs-vs refl refl x = refl

subst-splitCtx-cong-dep-triple-wkTy :
  ∀ {Δ} {C1 C2 : Ty Δ} {H1 : Ty (Δ , C1)} {H2 : Ty (Δ , C2)}
  → (eC : C1 ≡ C2)
  → (eH : subst (λ C → Ty (Δ , C)) eC H1 ≡ H2)
  → subst Ty (sym (splitCtx-cong-dep eC eH)) (wkTy (wkTy (wkTy H2)))
      ≡ wkTy (wkTy (wkTy H1))
subst-splitCtx-cong-dep-triple-wkTy refl refl = refl

subst-splitCtx-cong-dep-quadruple-wkTy :
  ∀ {Δ} {C1 C2 : Ty Δ} {H1 : Ty (Δ , C1)} {H2 : Ty (Δ , C2)}
  → (eC : C1 ≡ C2)
  → (eH : subst (λ C → Ty (Δ , C)) eC H1 ≡ H2)
  → subst Ty (sym (splitCtx-cong-dep eC eH))
      (wkTy (wkTy (wkTy (wkTy C2))))
    ≡ wkTy (wkTy (wkTy (wkTy C1)))
subst-splitCtx-cong-dep-quadruple-wkTy refl refl = refl

subst-splitCtx-cong-dep-quadruple-wkTy-any :
  ∀ {Δ} {C1 C2 : Ty Δ} {H1 : Ty (Δ , C1)} {H2 : Ty (Δ , C2)}
  → (eC : C1 ≡ C2)
  → (eH : subst (λ C → Ty (Δ , C)) eC H1 ≡ H2)
  → (T : Ty Δ)
  → subst Ty (sym (splitCtx-cong-dep eC eH))
      (wkTy (wkTy (wkTy (wkTy T))))
    ≡ wkTy (wkTy (wkTy (wkTy T)))
subst-splitCtx-cong-dep-quadruple-wkTy-any refl refl T = refl

subst-splitCtx-cong-dep-vs-vs-vs :
  ∀ {Δ} {C1 C2 : Ty Δ} {H1 : Ty (Δ , C1)} {H2 : Ty (Δ , C2)}
  → (eC : C1 ≡ C2)
  → (eH : subst (λ C → Ty (Δ , C)) eC H1 ≡ H2)
  → subst Var (sym (splitCtx-cong-dep eC eH)) (vs (vs (vs vz))) ≡ vs (vs (vs vz))
subst-splitCtx-cong-dep-vs-vs-vs refl refl = refl

subst-splitCtx-cong-dep-vs-vs-vs-vs :
  ∀ {Δ} {C1 C2 : Ty Δ} {H1 : Ty (Δ , C1)} {H2 : Ty (Δ , C2)}
  → (eC : C1 ≡ C2)
  → (eH : subst (λ C → Ty (Δ , C)) eC H1 ≡ H2)
  → (x : Var Δ)
  → subst Var (sym (splitCtx-cong-dep eC eH)) (vs (vs (vs (vs x)))) ≡
      vs (vs (vs (vs x)))
subst-splitCtx-cong-dep-vs-vs-vs-vs refl refl x = refl

```


## Step Package and Main Recursion

The next mutual block is the heart of the argument. It starts by stating the
four recursive theorems. The remainder of the block analyzes one pasting
extension in the two geometric branches and packages the resulting data into
`StepData`. The final clauses of `func-pasting`, `func-dangling`,
`func-dangling-type`, and `func-dangling-var` are then just projections from
that step package.

This is the point where the natural-language proof says:

1. recurse on the previous selector
2. obtain the recursive dangling witness `d`
3. identify the new functorial context with the standard extension built from `d`
4. transport the canonical dangling witnesses across that identification
5. read off the four required conclusions

The code below follows exactly that pattern.

```agda
{-# TERMINATING #-}
mutual
  func-pasting :
    ∀ {Γ} (Γps : CtxPs Γ)
    → (s : PsSel Γps)
    → CtxPs (Γ ↑ eval-ps-sel s)
  
  func-dangling :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel Γps)
    → VarPs (Γ ↑ eval-ps-sel s) (func-pasting Γps s)
  
  func-dangling-type :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel Γps)
    → varps-to-type (func-dangling xps s)
      ≡ varps-to-type xps [ in⁻ Γ (eval-ps-sel s) ]T
  
  func-dangling-var :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel Γps)
    → eval-ps-sel s (varps-to-var xps) ≡ false
    → var (varps-to-var xps) [ in⁻ Γ (eval-ps-sel s) ]t
      ≡ var (varps-to-var (func-dangling xps s))
  
  unsplit-step-hom-align :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → subst
        (λ B → Ty ((Γ ↑ prev-selector s) , B))
        (sym (func-dangling-type xps (prev-pssel s)))
        (hom-type-ext xps [ ⟨ wkSub (in⁻ Γ (prev-selector s)) , var vz ⟩ ]T)
      ≡ hom-type-ext (func-dangling xps (prev-pssel s))
  unsplit-step-hom-align {Γ} {Γps} xps s =
    subst-hom-ty-transport e base1 base2 u1 v1 u2 v2 e-base e-u e-v
    where
      X0 : Var Γ → Bool
      X0 = prev-selector s

      notSel : X0 (varps-to-var xps) ≡ false
      notSel = prev-selector-not-selected s
  
      d : VarPs (Γ ↑ X0) (func-pasting Γps (prev-pssel s))
      d = func-dangling xps (prev-pssel s)
  
      C1 : Ty (Γ ↑ X0)
      C1 = varps-to-type xps [ in⁻ Γ X0 ]T
  
      C2 : Ty (Γ ↑ X0)
      C2 = varps-to-type d
  
      e : C1 ≡ C2
      e = sym (func-dangling-type xps (prev-pssel s))
  
      snoc1 : Sub ((Γ ↑ X0) , C1) (Γ , varps-to-type xps)
      snoc1 = ⟨ wkSub (in⁻ Γ X0) , var vz ⟩
  
      base1 : Ty ((Γ ↑ X0) , C1)
      base1 = wkTy (varps-to-type xps) [ snoc1 ]T
  
      base2 : Ty ((Γ ↑ X0) , C2)
      base2 = wkTy C2
  
      u1 : Tm ((Γ ↑ X0) , C1)
      u1 = var (vs (varps-to-var xps)) [ snoc1 ]t
  
      v1 : Tm ((Γ ↑ X0) , C1)
      v1 = var vz [ snoc1 ]t
  
      u2 : Tm ((Γ ↑ X0) , C2)
      u2 = var (vs (varps-to-var d))
  
      v2 : Tm ((Γ ↑ X0) , C2)
      v2 = var vz
  
      base1-to-wkC1 : base1 ≡ wkTy C1
      base1-to-wkC1 =
        trans (wkTy-sub (varps-to-type xps) (wkSub (in⁻ Γ X0)) (var vz))
          (wkTy-[]T (varps-to-type xps) (in⁻ Γ X0))
  
      e-base : subst (λ C → Ty ((Γ ↑ X0) , C)) e base1 ≡ base2
      e-base =
        trans (cong (subst (λ C → Ty ((Γ ↑ X0) , C)) e) base1-to-wkC1)
          (trans (subst-wkTy-transport e C1)
            (cong (λ Z → wkTy {A = C2} Z) e))
  
      u1-to-u2 : u1 ≡ var (vs (varps-to-var d))
      u1-to-u2 =
        trans (lookup-wkSub (varps-to-var xps) (in⁻ Γ X0))
          (cong wkTm
            (func-dangling-var xps (prev-pssel s) notSel))
  
      e-u : subst (λ C → Tm ((Γ ↑ X0) , C)) e u1 ≡ u2
      e-u =
        trans (cong (subst (λ C → Tm ((Γ ↑ X0) , C)) e) u1-to-u2)
          (subst-var-vs e (varps-to-var d))
  
      e-v : subst (λ C → Tm ((Γ ↑ X0) , C)) e v1 ≡ v2
      e-v = subst-var-vz e
  
  -- In the unsplit case, the functorial image of the extension is exactly the
  -- ordinary pasting extension generated by the recursive dangling witness `d`.
  unsplit-step-align :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → ((ext-ctx xps) ↑ eval-step-unsplit (prev-pssel s))
        ≡ ext-ctx (func-dangling xps (prev-pssel s))
  unsplit-step-align xps s =
    snocCtx-cong-dep
      (sym (func-dangling-type xps (prev-pssel s)))
      (unsplit-step-hom-align xps s)
  
  -- In the split case, the image is the extension generated by the new edge on `d`.
  split-step-align :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → ((ext-ctx xps) ↑ eval-step-split (prev-pssel s))
        ≡ ext-ctx (varps-f (func-dangling xps (prev-pssel s)))
  split-step-align xps s =
    splitCtx-cong-dep
      (sym (func-dangling-type xps (prev-pssel s)))
      (unsplit-step-hom-align xps s)
  
  -- These target-type lemmas compute what substitution by `in⁻` does to the
  -- three canonical dangling witnesses `f`, `y`, and an older weakened witness.
  -- They are the raw computations later compared against the canonical types of
  -- the transported witnesses in the aligned branch contexts.
  unsplit-f-target-type :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → varps-to-type (varps-f xps)
        [ in⁻ (ext-ctx xps)
            (eval-step-unsplit (prev-pssel s)) ]T
      ≡ wkTy (hom-type-ext xps [ ⟨ wkSub (in⁻ Γ (prev-selector s)) , var vz ⟩ ]T)
  unsplit-f-target-type {Γ} xps s =
    trans
      (wkTy-sub (hom-type-ext xps)
        (wkSub (⟨ wkSub (in⁻ Γ (prev-selector s)) , var vz ⟩)) (var vz))
      (wkTy-[]T (hom-type-ext xps)
        (⟨ wkSub (in⁻ Γ (prev-selector s)) , var vz ⟩))
  
  split-f-target-type :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → varps-to-type (varps-f xps)
        [ in⁻ (ext-ctx xps)
            (eval-step-split (prev-pssel s)) ]T
      ≡ wkTy (wkTy (wkTy (hom-type-ext xps [ ⟨ wkSub (in⁻ Γ (prev-selector s)) , var vz ⟩ ]T)))
  split-f-target-type {Γ} xps s =
    trans
      (wkTy-sub (hom-type-ext xps)
        (wkSub (wkSub (wkSub (⟨ wkSub (in⁻ Γ (prev-selector s)) , var vz ⟩))))
        (var (vs (vs vz))))
      (trans
        (wkTy-[]T (hom-type-ext xps)
          (wkSub (wkSub (⟨ wkSub (in⁻ Γ (prev-selector s)) , var vz ⟩))))
        (trans
          (cong wkTy
            (wkTy-[]T (hom-type-ext xps)
              (wkSub (⟨ wkSub (in⁻ Γ (prev-selector s)) , var vz ⟩))))
          (cong (λ Z → wkTy (wkTy Z))
            (wkTy-[]T (hom-type-ext xps)
              (⟨ wkSub (in⁻ Γ (prev-selector s)) , var vz ⟩)))))
  
  -- Generic lemma for how `wkTy (wkTy T)` interacts with the unsplit inclusion.
  -- Subsumes the old `unsplit-y-target-type` (T = varps-to-type xps) and
  -- `unsplit-weak-target-type` (T = varps-to-type zps).
  unsplit-wk2-target-type :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → (T : Ty Γ)
    → wkTy (wkTy T)
        [ in⁻ (ext-ctx xps)
            (eval-step-unsplit (prev-pssel s)) ]T
      ≡ wkTy (wkTy (T [ in⁻ Γ (prev-selector s) ]T))
  unsplit-wk2-target-type {Γ} xps s T =
    trans
      (wkTy-sub (wkTy T)
        (wkSub (in⁻ ((Γ , varps-to-type xps))
          (λ where
            vz → false
            (vs x) → prev-selector s x)))
        (var vz))
      (trans
        (wkTy-sub T
          (wkSub (wkSub (in⁻ Γ (prev-selector s))))
          (var (vs vz)))
        (trans
          (wkTy-[]T T (wkSub (in⁻ Γ (prev-selector s))))
          (cong wkTy
            (wkTy-[]T T (in⁻ Γ (prev-selector s))))))

  -- Generic lemma for how `wkTy (wkTy T)` interacts with the split inclusion.
  -- Subsumes the old `split-y-target-type` and `split-weak-target-type`.
  split-wk2-target-type :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → (T : Ty Γ)
    → wkTy (wkTy T)
        [ in⁻ (ext-ctx xps)
            (eval-step-split (prev-pssel s)) ]T
      ≡ wkTy (wkTy (wkTy (wkTy (T [ in⁻ Γ (prev-selector s) ]T))))
  split-wk2-target-type {Γ} xps s T =
    trans
      (wkTy-sub (wkTy T)
        (wkSub (wkSub (wkSub
          (in⁻ ((Γ , varps-to-type xps))
            (λ where
              vz → false
              (vs x) → prev-selector s x)))))
        (var (vs (vs vz))))
      (trans
        (wkTy-sub T
          (wkSub (wkSub (wkSub (wkSub (in⁻ Γ (prev-selector s))))))
          (var (vs (vs (vs vz)))))
        (trans
          (wkTy-[]T T
            (wkSub (wkSub (wkSub (in⁻ Γ (prev-selector s))))))
          (trans
            (cong wkTy
              (wkTy-[]T T
                (wkSub (wkSub (in⁻ Γ (prev-selector s))))))
            (trans
              (cong (λ Z → wkTy (wkTy Z))
                (wkTy-[]T T
                  (wkSub (in⁻ Γ (prev-selector s)))))
              (cong (λ Z → wkTy (wkTy (wkTy Z)))
                (wkTy-[]T T
                  (in⁻ Γ (prev-selector s))))))))
  
  unsplit-y-target-var :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → var (vs vz) [ in⁻ (ext-ctx xps)
        (eval-step-unsplit (prev-pssel s)) ]t
      ≡ var (vs vz)
  unsplit-y-target-var {Γ} xps s =
    trans
      (lookup-wkSub vz (in⁻ ((Γ , varps-to-type xps)) Y))
      (cong wkTm (lookup-vz-in⁻-unsplit (varps-to-type xps) Y refl))
    where
      Y : Var (Γ , varps-to-type xps) → Bool
      Y vz = false
      Y (vs x) = prev-selector s x
  
  split-y-target-var :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → var (vs vz) [ in⁻ (ext-ctx xps)
        (eval-step-split (prev-pssel s)) ]t
      ≡ var (vs (vs (vs vz)))
  split-y-target-var {Γ} xps s =
    trans
      (lookup-wkSub vz (wkSub (wkSub (in⁻ ((Γ , varps-to-type xps)) Y))))
      (trans
        (cong wkTm (lookup-wkSub vz (wkSub (in⁻ ((Γ , varps-to-type xps)) Y))))
        (trans
          (cong (λ t → wkTm (wkTm t))
            (lookup-wkSub vz (in⁻ ((Γ , varps-to-type xps)) Y)))
          (cong (λ t → wkTm (wkTm (wkTm t)))
            (lookup-vz-in⁻-unsplit (varps-to-type xps) Y refl))))
    where
      Y : Var (Γ , varps-to-type xps) → Bool
      Y vz = false
      Y (vs x) = prev-selector s x
  
  -- After transporting `varps-f d` across the unsplit alignment, its type is
  -- exactly the old `f`-type pushed forward along `in⁻`.
  unsplit-f-step-type :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → varps-to-type
        (transport-VarPs (sym (unsplit-step-align xps s))
          (varps-f (func-dangling xps (prev-pssel s))))
      ≡ varps-to-type (varps-f xps)
          [ in⁻ (ext-ctx xps)
              (eval-step-unsplit (prev-pssel s)) ]T
  unsplit-f-step-type {Γ} {Γps} xps s =
    trans
      (varps-to-type-transport (sym eq) (varps-f d))
      (trans
        (subst-snocCtx-cong-dep-wkTy eC eH)
        (sym (unsplit-f-target-type xps s)))
    where
      d = func-dangling xps (prev-pssel s)
      eC = sym (func-dangling-type xps (prev-pssel s))
      eH = unsplit-step-hom-align xps s
      eq = unsplit-step-align xps s
  
  -- In the split branch, the image of the old edge `f` is represented by
  -- `varps-y (varps-f d)`, and this lemma identifies its transported type.
  split-f-step-type :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → varps-to-type
        (transport-VarPs (sym (split-step-align xps s))
          (varps-y (varps-f (func-dangling xps (prev-pssel s)))))
      ≡ varps-to-type (varps-f xps)
          [ in⁻ (ext-ctx xps)
              (eval-step-split (prev-pssel s)) ]T
  split-f-step-type {Γ} {Γps} xps s =
    trans
      (varps-to-type-transport (sym eq) (varps-y (varps-f d)))
      (trans
        (subst-splitCtx-cong-dep-triple-wkTy eC eH)
        (sym (split-f-target-type xps s)))
    where
      d = func-dangling xps (prev-pssel s)
      eC = sym (func-dangling-type xps (prev-pssel s))
      eH = unsplit-step-hom-align xps s
      eq = split-step-align xps s
  
  unsplit-y-step-type :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → varps-to-type
        (transport-VarPs (sym (unsplit-step-align xps s))
          (varps-y (func-dangling xps (prev-pssel s))))
      ≡ varps-to-type (varps-y xps)
          [ in⁻ (ext-ctx xps)
              (eval-step-unsplit (prev-pssel s)) ]T
  unsplit-y-step-type {Γ} {Γps} xps s =
    trans
      (varps-to-type-transport (sym eq) (varps-y d))
      (trans
        (subst-snocCtx-cong-dep-double-wkTy eC eH)
        (sym (unsplit-wk2-target-type xps s (varps-to-type xps))))
    where
      X0 = prev-selector s
      d = func-dangling xps (prev-pssel s)
      eC = sym (func-dangling-type xps (prev-pssel s))
      eH = unsplit-step-hom-align xps s
      eq = unsplit-step-align xps s
  
  split-y-step-type :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → varps-to-type
        (transport-VarPs (sym (split-step-align xps s))
          (varps-weak (varps-f (func-dangling xps (prev-pssel s)))
            (varps-y (func-dangling xps (prev-pssel s)))
            (lt-varps-y-varps-f (func-dangling xps (prev-pssel s)))))
      ≡ varps-to-type (varps-y xps)
          [ in⁻ (ext-ctx xps)
              (eval-step-split (prev-pssel s)) ]T
  split-y-step-type {Γ} {Γps} xps s =
    trans
      (varps-to-type-transport (sym eq)
        (varps-weak (varps-f d) (varps-y d) (lt-varps-y-varps-f d)))
      (trans
        (subst-splitCtx-cong-dep-quadruple-wkTy eC eH)
        (sym (split-wk2-target-type xps s (varps-to-type xps))))
    where
      X0 = prev-selector s
      d = func-dangling xps (prev-pssel s)
      eC = sym (func-dangling-type xps (prev-pssel s))
      eH = unsplit-step-hom-align xps s
      eq = split-step-align xps s
  
  prev-dangling-dim :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → (zps : VarPs Γ Γps)
    → dim-ty (varps-to-type (func-dangling zps (prev-pssel s)))
      ≡ dim-ty (varps-to-type zps)
  prev-dangling-dim xps s zps =
    trans (cong dim-ty (func-dangling-type zps (prev-pssel s)))
      (dim-ty-sub (varps-to-type zps) (in⁻ _ (prev-selector s)))
  
  lift-prev-dangling-dim-lt :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → (zps : VarPs Γ Γps)
    → dim-ty (varps-to-type zps) < dim-ty (varps-to-type xps)
    → dim-ty (varps-to-type (func-dangling zps (prev-pssel s)))
      < dim-ty (varps-to-type (func-dangling xps (prev-pssel s)))
  lift-prev-dangling-dim-lt xps s zps lt =
    <-cong
      (sym (prev-dangling-dim xps s zps))
      (sym (prev-dangling-dim xps s xps))
      lt
  
  lift-split-prev-dangling-dim-lt :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → (zps : VarPs Γ Γps)
    → (lt : dim-ty (varps-to-type zps) < dim-ty (varps-to-type xps))
    → dim-ty
        (varps-to-type
          (varps-weak
            (func-dangling xps (prev-pssel s))
            (func-dangling zps (prev-pssel s))
            (lift-prev-dangling-dim-lt xps s zps lt)))
      < dim-ty (varps-to-type (varps-f (func-dangling xps (prev-pssel s))))
  lift-split-prev-dangling-dim-lt xps s zps lt =
    <-cong
      (sym
        (dim-varps-weak
          (func-dangling xps (prev-pssel s))
          (func-dangling zps (prev-pssel s))
          (lift-prev-dangling-dim-lt xps s zps lt)))
      refl
      (<-trans (lift-prev-dangling-dim-lt xps s zps lt)
        (lt-varps-to-f (func-dangling xps (prev-pssel s))))
  
  unsplit-weak-step-type :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → (zps : VarPs Γ Γps)
    → (lt : dim-ty (varps-to-type zps) < dim-ty (varps-to-type xps))
    → varps-to-type
        (transport-VarPs (sym (unsplit-step-align xps s))
          (varps-weak (func-dangling xps (prev-pssel s))
            (func-dangling zps (prev-pssel s))
            (lift-prev-dangling-dim-lt xps s zps lt)))
      ≡ varps-to-type (varps-weak xps zps lt)
          [ in⁻ (ext-ctx xps)
              (eval-step-unsplit (prev-pssel s)) ]T
  unsplit-weak-step-type {Γ} {Γps} xps s zps lt =
    trans
      (varps-to-type-transport (sym eq)
        (varps-weak d dz lt'))
      (trans
        (subst-snocCtx-cong-dep-double-wkTy-any eC eH (varps-to-type dz))
        (trans
          (cong (λ Z → wkTy (wkTy Z))
            (func-dangling-type zps (prev-pssel s)))
          (sym (unsplit-wk2-target-type xps s (varps-to-type zps)))))
    where
      X0 = prev-selector s
      d = func-dangling xps (prev-pssel s)
      dz = func-dangling zps (prev-pssel s)
      lt' = lift-prev-dangling-dim-lt xps s zps lt
      eC = sym (func-dangling-type xps (prev-pssel s))
      eH = unsplit-step-hom-align xps s
      eq = unsplit-step-align xps s
  
  split-weak-step-type :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → (zps : VarPs Γ Γps)
    → (lt : dim-ty (varps-to-type zps) < dim-ty (varps-to-type xps))
    → varps-to-type
        (transport-VarPs (sym (split-step-align xps s))
          (varps-weak
            (varps-f (func-dangling xps (prev-pssel s)))
            (varps-weak (func-dangling xps (prev-pssel s))
              (func-dangling zps (prev-pssel s))
              (lift-prev-dangling-dim-lt xps s zps lt))
            (lift-split-prev-dangling-dim-lt xps s zps lt)))
      ≡ varps-to-type (varps-weak xps zps lt)
          [ in⁻ (ext-ctx xps)
              (eval-step-split (prev-pssel s)) ]T
  split-weak-step-type {Γ} {Γps} xps s zps lt =
    trans
      (varps-to-type-transport (sym eq)
        (varps-weak (varps-f d) (varps-weak d dz lt') lt''))
      (trans
        (subst-splitCtx-cong-dep-quadruple-wkTy-any eC eH (varps-to-type dz))
        (trans
          (cong (λ Z → wkTy (wkTy (wkTy (wkTy Z))))
            (func-dangling-type zps (prev-pssel s)))
          (sym (split-wk2-target-type xps s (varps-to-type zps)))))
    where
      X0 = prev-selector s
      d = func-dangling xps (prev-pssel s)
      dz = func-dangling zps (prev-pssel s)
      lt' = lift-prev-dangling-dim-lt xps s zps lt
      lt'' = lift-split-prev-dangling-dim-lt xps s zps lt
      eC = sym (func-dangling-type xps (prev-pssel s))
      eH = unsplit-step-hom-align xps s
      eq = split-step-align xps s
  
  unsplit-f-step-var :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → var vz [ in⁻ (ext-ctx xps)
        (eval-step-unsplit (prev-pssel s)) ]t
      ≡ var
          (varps-to-var
            (transport-VarPs (sym (unsplit-step-align xps s))
              (varps-f (func-dangling xps (prev-pssel s)))))
  unsplit-f-step-var {Γ} {Γps} xps s =
    sym
      (trans
        (cong var
          (varps-to-var-transport (sym eq) (varps-f d)))
        (cong var (subst-snocCtx-cong-dep-vz eC eH)))
    where
      d = func-dangling xps (prev-pssel s)
      eC = sym (func-dangling-type xps (prev-pssel s))
      eH = unsplit-step-hom-align xps s
      eq = unsplit-step-align xps s
  
  unsplit-y-step-var :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → var (vs vz) [ in⁻ (ext-ctx xps)
        (eval-step-unsplit (prev-pssel s)) ]t
      ≡ var
          (varps-to-var
            (transport-VarPs (sym (unsplit-step-align xps s))
              (varps-y (func-dangling xps (prev-pssel s)))))
  unsplit-y-step-var {Γ} {Γps} xps s =
    trans
      (unsplit-y-target-var xps s)
      (sym
        (trans
          (cong var
            (varps-to-var-transport (sym eq) (varps-y d)))
          (cong var (subst-snocCtx-cong-dep-vs-vz eC eH))))
    where
      d = func-dangling xps (prev-pssel s)
      eC = sym (func-dangling-type xps (prev-pssel s))
      eH = unsplit-step-hom-align xps s
      eq = unsplit-step-align xps s
  
  split-y-step-var :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → var (vs vz) [ in⁻ (ext-ctx xps)
        (eval-step-split (prev-pssel s)) ]t
      ≡ var
          (varps-to-var
            (transport-VarPs (sym (split-step-align xps s))
              (varps-weak (varps-f (func-dangling xps (prev-pssel s)))
                (varps-y (func-dangling xps (prev-pssel s)))
                (lt-varps-y-varps-f (func-dangling xps (prev-pssel s))))))
  split-y-step-var {Γ} {Γps} xps s =
    trans
      (split-y-target-var xps s)
      (sym
        (trans
          (cong var
            (varps-to-var-transport (sym eq)
              (varps-weak (varps-f d) (varps-y d) (lt-varps-y-varps-f d))))
          (cong var (subst-splitCtx-cong-dep-vs-vs-vs eC eH))))
    where
      d = func-dangling xps (prev-pssel s)
      eC = sym (func-dangling-type xps (prev-pssel s))
      eH = unsplit-step-hom-align xps s
      eq = split-step-align xps s
  
  unsplit-weak-target-var :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (zps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → prev-selector s (varps-to-var zps) ≡ false
    → var (vs (vs (varps-to-var zps))) [ in⁻ (ext-ctx xps)
        (eval-step-unsplit (prev-pssel s)) ]t
      ≡ var (vs (vs (varps-to-var (func-dangling zps (prev-pssel s)))))
  unsplit-weak-target-var {Γ} xps zps s notSel =
    trans
      (lookup-wkSub (vs (varps-to-var zps)) (in⁻ ((Γ , varps-to-type xps)) Y))
      (trans
        (cong wkTm (lookup-wkSub (varps-to-var zps) (in⁻ Γ (prev-selector s))))
        (cong (λ t → wkTm (wkTm t))
          (func-dangling-var zps (prev-pssel s) notSel)))
    where
      Y : Var (Γ , varps-to-type xps) → Bool
      Y vz = false
      Y (vs x) = prev-selector s x
  
  split-weak-target-var :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (zps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → prev-selector s (varps-to-var zps) ≡ false
    → var (vs (vs (varps-to-var zps))) [ in⁻ (ext-ctx xps)
        (eval-step-split (prev-pssel s)) ]t
      ≡ var
          (vs (vs (vs (vs (varps-to-var
            (func-dangling zps (prev-pssel s)))))))
  split-weak-target-var {Γ} xps zps s notSel =
    trans
      (lookup-wkSub (vs (varps-to-var zps))
        (wkSub (wkSub (in⁻ ((Γ , varps-to-type xps)) Y))))
      (trans
        (cong wkTm
          (lookup-wkSub (vs (varps-to-var zps))
            (wkSub (in⁻ ((Γ , varps-to-type xps)) Y))))
        (trans
          (cong (λ t → wkTm (wkTm t))
            (lookup-wkSub (vs (varps-to-var zps))
              (in⁻ ((Γ , varps-to-type xps)) Y)))
          (trans
            (cong (λ t → wkTm (wkTm (wkTm t)))
              (lookup-wkSub (varps-to-var zps) (in⁻ Γ (prev-selector s))))
            (cong (λ t → wkTm (wkTm (wkTm (wkTm t))))
              (func-dangling-var zps (prev-pssel s) notSel)))))
    where
      Y : Var (Γ , varps-to-type xps) → Bool
      Y vz = false
      Y (vs x) = prev-selector s x
  
  unsplit-weak-step-var :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → (zps : VarPs Γ Γps)
    → (lt : dim-ty (varps-to-type zps) < dim-ty (varps-to-type xps))
    → eval-step-unsplit {xps = xps} (prev-pssel s)
        (vs (vs (varps-to-var zps))) ≡ false
    → var (vs (vs (varps-to-var zps))) [ in⁻ (ext-ctx xps)
        (eval-step-unsplit {xps = xps} (prev-pssel s)) ]t
      ≡ var
          (varps-to-var
            (transport-VarPs (sym (unsplit-step-align xps s))
              (varps-weak (func-dangling xps (prev-pssel s))
                (func-dangling zps (prev-pssel s))
                (lift-prev-dangling-dim-lt xps s zps lt))))
  unsplit-weak-step-var {Γ} {Γps} xps s zps lt notSel =
    trans
      (unsplit-weak-target-var xps zps s notSel)
      (sym
        (trans
          (cong var
            (varps-to-var-transport (sym eq)
              (varps-weak d dz lt')))
          (cong var
            (subst-snocCtx-cong-dep-vs-vs eC eH (varps-to-var dz)))))
    where
      d = func-dangling xps (prev-pssel s)
      dz = func-dangling zps (prev-pssel s)
      lt' = lift-prev-dangling-dim-lt xps s zps lt
      eC = sym (func-dangling-type xps (prev-pssel s))
      eH = unsplit-step-hom-align xps s
      eq = unsplit-step-align xps s
  
  split-weak-step-var :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → (zps : VarPs Γ Γps)
    → (lt : dim-ty (varps-to-type zps) < dim-ty (varps-to-type xps))
    → eval-step-split {xps = xps} (prev-pssel s)
        (vs (vs (varps-to-var zps))) ≡ false
    → var (vs (vs (varps-to-var zps))) [ in⁻ (ext-ctx xps)
        (eval-step-split {xps = xps} (prev-pssel s)) ]t
      ≡ var
          (varps-to-var
            (transport-VarPs (sym (split-step-align xps s))
              (varps-weak
                (varps-f (func-dangling xps (prev-pssel s)))
                (varps-weak (func-dangling xps (prev-pssel s))
                  (func-dangling zps (prev-pssel s))
                  (lift-prev-dangling-dim-lt xps s zps lt))
                (lift-split-prev-dangling-dim-lt xps s zps lt))))
  split-weak-step-var {Γ} {Γps} xps s zps lt notSel =
    trans
      (split-weak-target-var xps zps s notSel)
      (sym
        (trans
          (cong var
            (varps-to-var-transport (sym eq)
              (varps-weak (varps-f d)
                (varps-weak d dz lt')
                lt'')))
          (cong var
            (subst-splitCtx-cong-dep-vs-vs-vs-vs eC eH (varps-to-var dz)))))
    where
      d = func-dangling xps (prev-pssel s)
      dz = func-dangling zps (prev-pssel s)
      lt' = lift-prev-dangling-dim-lt xps s zps lt
      lt'' = lift-split-prev-dangling-dim-lt xps s zps lt
      eC = sym (func-dangling-type xps (prev-pssel s))
      eH = unsplit-step-hom-align xps s
      eq = split-step-align xps s
  
  -- `StepData` is the packaged output of the one-step branch analysis. The
  -- main recursive theorem only needs to project fields from this record.
  -- `StepData` packages the entire one-step geometric analysis. The point is
  -- that once we know which branch we are in, all four recursive outputs are
  -- obtained by transporting standard dangling witnesses from the canonical
  -- branch context. The final recursive clauses can then be simple projections.
  record StepData {Γ : Ctx} {Γps : CtxPs Γ}
    (xps : VarPs Γ Γps) (s : PsSel (ps-ext xps)) : Set where
    field
      -- The resulting pasting structure on the functorial image.
      pasting : CtxPs ((ext-ctx xps) ↑ eval-ext-sel s)
      -- The transported witness corresponding to the newest edge `f`.
      danglingF : VarPs ((ext-ctx xps) ↑ eval-ext-sel s) pasting
      danglingFType :
        varps-to-type danglingF
          ≡ varps-to-type (varps-f xps) [ in⁻ (ext-ctx xps) (eval-ext-sel s) ]T
      danglingFVar :
        eval-ext-sel s vz ≡ false
        → var vz [ in⁻ (ext-ctx xps) (eval-ext-sel s) ]t
          ≡ var (varps-to-var danglingF)
      -- The transported witness corresponding to the new target `y`.
      danglingY : VarPs ((ext-ctx xps) ↑ eval-ext-sel s) pasting
      danglingYType :
        varps-to-type danglingY
          ≡ varps-to-type (varps-y xps) [ in⁻ (ext-ctx xps) (eval-ext-sel s) ]T
      danglingYVar :
        var (vs vz) [ in⁻ (ext-ctx xps) (eval-ext-sel s) ]t
          ≡ var (varps-to-var danglingY)
      -- The transported witness for any older dangling variable that survives the step.
      danglingWeak :
        (zps : VarPs Γ Γps)
        → dim-ty (varps-to-type zps) < dim-ty (varps-to-type xps)
        → VarPs ((ext-ctx xps) ↑ eval-ext-sel s) pasting
      danglingWeakType :
        (zps : VarPs Γ Γps)
        → (lt : dim-ty (varps-to-type zps) < dim-ty (varps-to-type xps))
        → varps-to-type (danglingWeak zps lt)
          ≡ varps-to-type (varps-weak xps zps lt)
              [ in⁻ (ext-ctx xps) (eval-ext-sel s) ]T
      danglingWeakVar :
        (zps : VarPs Γ Γps)
        → (lt : dim-ty (varps-to-type zps) < dim-ty (varps-to-type xps))
        → eval-ext-sel s (vs (vs (varps-to-var zps))) ≡ false
        → var (vs (vs (varps-to-var zps))) [ in⁻ (ext-ctx xps) (eval-ext-sel s) ]t
          ≡ var (varps-to-var (danglingWeak zps lt))
  
  -- Constructing `StepData` is precisely where the proof branches
  -- geometrically. The unsplit branch reuses the canonical witnesses over `d`,
  -- while the split branch reuses those over `varps-f d`.
  step-data :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → StepData xps s
  step-data xps (unsplitSel X0 lm0 notSel) =
    let eq = unsplit-step-align xps (unsplitSel X0 lm0 notSel)
        d = func-dangling xps X0
    in record
         { pasting = subst CtxPs (sym eq) (ps-ext d)
         ; danglingF = transport-VarPs (sym eq) (varps-f d)
         ; danglingFType = unsplit-f-step-type xps (unsplitSel X0 lm0 notSel)
         ; danglingFVar = λ _ → unsplit-f-step-var xps (unsplitSel X0 lm0 notSel)
         ; danglingY = transport-VarPs (sym eq) (varps-y d)
         ; danglingYType = unsplit-y-step-type xps (unsplitSel X0 lm0 notSel)
         ; danglingYVar = unsplit-y-step-var xps (unsplitSel X0 lm0 notSel)
         ; danglingWeak = λ zps lt →
             transport-VarPs (sym eq)
               (varps-weak d (func-dangling zps X0)
                 (lift-prev-dangling-dim-lt xps (unsplitSel X0 lm0 notSel) zps lt))
         ; danglingWeakType = λ zps lt →
             unsplit-weak-step-type xps (unsplitSel X0 lm0 notSel) zps lt
         ; danglingWeakVar = λ zps lt →
             unsplit-weak-step-var xps (unsplitSel X0 lm0 notSel) zps lt
         }
  step-data xps (splitSel X0 lm0 notSel) =
    let eq = split-step-align xps (splitSel X0 lm0 notSel)
        d = func-dangling xps X0
    in record
         { pasting = subst CtxPs (sym eq) (ps-ext (varps-f d))
         ; danglingF = transport-VarPs (sym eq) (varps-y (varps-f d))
         ; danglingFType = split-f-step-type xps (splitSel X0 lm0 notSel)
         ; danglingFVar = λ ()
         ; danglingY = transport-VarPs (sym eq)
             (varps-weak (varps-f d) (varps-y d) (lt-varps-y-varps-f d))
         ; danglingYType = split-y-step-type xps (splitSel X0 lm0 notSel)
         ; danglingYVar = split-y-step-var xps (splitSel X0 lm0 notSel)
         ; danglingWeak = λ zps lt →
             transport-VarPs (sym eq)
               (varps-weak
                 (varps-f d)
                 (varps-weak d (func-dangling zps X0)
                   (lift-prev-dangling-dim-lt xps (splitSel X0 lm0 notSel) zps lt))
                 (lift-split-prev-dangling-dim-lt xps (splitSel X0 lm0 notSel) zps lt))
         ; danglingWeakType = λ zps lt →
             split-weak-step-type xps (splitSel X0 lm0 notSel) zps lt
         ; danglingWeakVar = λ zps lt →
             split-weak-step-var xps (splitSel X0 lm0 notSel) zps lt
         }
  
  -- The rest of the mutual block simply exposes the relevant fields of `StepData`.
  step-pasting :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → CtxPs ((ext-ctx xps) ↑ eval-ext-sel s)
  step-pasting xps s =
    StepData.pasting (step-data xps s)
  
  step-dangling-f :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → VarPs ((ext-ctx xps) ↑ eval-ext-sel s) (step-pasting xps s)
  step-dangling-f xps s =
    StepData.danglingF (step-data xps s)
  
  step-dangling-f-type :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → varps-to-type (step-dangling-f xps s)
      ≡ varps-to-type (varps-f xps) [ in⁻ (ext-ctx xps) (eval-ext-sel s) ]T
  step-dangling-f-type xps s =
    StepData.danglingFType (step-data xps s)
  
  step-dangling-f-var :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → eval-ext-sel s vz ≡ false
    → var vz [ in⁻ (ext-ctx xps) (eval-ext-sel s) ]t
      ≡ var (varps-to-var (step-dangling-f xps s))
  step-dangling-f-var xps s notSel =
    StepData.danglingFVar (step-data xps s) notSel
  
  step-dangling-y :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → VarPs ((ext-ctx xps) ↑ eval-ext-sel s) (step-pasting xps s)
  step-dangling-y xps s =
    StepData.danglingY (step-data xps s)
  
  step-dangling-y-type :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → varps-to-type (step-dangling-y xps s)
      ≡ varps-to-type (varps-y xps) [ in⁻ (ext-ctx xps) (eval-ext-sel s) ]T
  step-dangling-y-type xps s =
    StepData.danglingYType (step-data xps s)
  
  step-dangling-y-var :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (s : PsSel (ps-ext xps))
    → eval-ext-sel s (vs vz) ≡ false
    → var (vs vz) [ in⁻ (ext-ctx xps) (eval-ext-sel s) ]t
      ≡ var (varps-to-var (step-dangling-y xps s))
  step-dangling-y-var xps s _ =
    StepData.danglingYVar (step-data xps s)
  
  step-dangling-weak :
    ∀ {Γ} {Γps : CtxPs Γ} (xps zps : VarPs Γ Γps)
    → (lt : dim-ty (varps-to-type zps) < dim-ty (varps-to-type xps))
    → (s : PsSel (ps-ext xps))
    → VarPs ((ext-ctx xps) ↑ eval-ext-sel s) (step-pasting xps s)
  step-dangling-weak xps zps lt s =
    StepData.danglingWeak (step-data xps s) zps lt
  
  step-dangling-weak-type :
    ∀ {Γ} {Γps : CtxPs Γ} (xps zps : VarPs Γ Γps)
    → (lt : dim-ty (varps-to-type zps) < dim-ty (varps-to-type xps))
    → (s : PsSel (ps-ext xps))
    → varps-to-type (step-dangling-weak xps zps lt s)
      ≡ varps-to-type (varps-weak xps zps lt)
          [ in⁻ (ext-ctx xps) (eval-ext-sel s) ]T
  step-dangling-weak-type xps zps lt s =
    StepData.danglingWeakType (step-data xps s) zps lt
  
  step-dangling-weak-var :
    ∀ {Γ} {Γps : CtxPs Γ} (xps zps : VarPs Γ Γps)
    → (lt : dim-ty (varps-to-type zps) < dim-ty (varps-to-type xps))
    → (s : PsSel (ps-ext xps))
    → eval-ext-sel s (vs (vs (varps-to-var zps))) ≡ false
    → var (vs (vs (varps-to-var zps))) [ in⁻ (ext-ctx xps) (eval-ext-sel s) ]t
      ≡ var (varps-to-var (step-dangling-weak xps zps lt s))
  step-dangling-weak-var xps zps lt s notSel =
    StepData.danglingWeakVar (step-data xps s) zps lt notSel
  
  -- Once the step package is available, the recursive theorem itself becomes
  -- short: the base case is immediate, and the extension case is just field
  -- projection from `StepData`.
  func-pasting ps-ob pssel-ob-unsplit = ps-ob
  func-pasting ps-ob pssel-ob-split = ps-ext varps-ob
  func-pasting (ps-ext xps) s = step-pasting xps s
  
  func-dangling {Γps = ps-ob} varps-ob pssel-ob-unsplit = varps-ob
  func-dangling {Γps = ps-ob} varps-ob pssel-ob-split = varps-y varps-ob
  func-dangling {Γps = ps-ext xps} (varps-f .xps) s =
    step-dangling-f xps s
  func-dangling {Γps = ps-ext xps} (varps-y .xps) s =
    step-dangling-y xps s
  func-dangling {Γps = ps-ext xps} (varps-weak .xps zps lt) s =
    step-dangling-weak xps zps lt s
  
  func-dangling-type {Γps = ps-ob} varps-ob pssel-ob-unsplit = refl
  func-dangling-type {Γps = ps-ob} varps-ob pssel-ob-split = refl
  func-dangling-type {Γps = ps-ext xps} (varps-f .xps) s =
    step-dangling-f-type xps s
  func-dangling-type {Γps = ps-ext xps} (varps-y .xps) s =
    step-dangling-y-type xps s
  func-dangling-type {Γps = ps-ext xps} (varps-weak .xps zps lt) s =
    step-dangling-weak-type xps zps lt s
  
  func-dangling-var {Γps = ps-ob} varps-ob pssel-ob-unsplit notSel = refl
  func-dangling-var {Γps = ps-ob} varps-ob pssel-ob-split ()
  func-dangling-var {Γps = ps-ext xps} (varps-f .xps) s notSel =
    step-dangling-f-var xps s notSel
  func-dangling-var {Γps = ps-ext xps} (varps-y .xps) s notSel =
    step-dangling-y-var xps s notSel
  func-dangling-var {Γps = ps-ext xps} (varps-weak .xps zps lt) s notSel =
    step-dangling-weak-var xps zps lt s notSel
  
  ```

## Raw Bridge

The structured selector proof above is the robust proof engine, but later functoriality modules still speak in terms of raw selectors
`X : Var Γ → Bool`. This section reifies such a selector into a structured selector `PsSel`, proves that evaluation recovers the original boolean function, and then transports the main theorem back to the raw interface.

Conceptually, this is the final step of the natural-language proof: structured
selectors are the right induction principle for the formal argument, but the
mathematical statement is still about ordinary selectors. So we show that every
legal raw selector can be re-packaged as a `PsSel`, and that this packaging is
definitionally faithful enough to transport the four main theorems back.

```agda
abstract
  subst-var-transport :
    ∀ {Γ Γ'} (eq : Γ ≡ Γ') (x : Var Γ)
    → subst Tm eq (var x) ≡ var (subst Var eq x)
  subst-var-transport refl x = refl

mutual
  -- Reify a legal raw selector into the structured selector used by the main proof.
  reify-pssel :
    ∀ {Γ} (Γps : CtxPs Γ)
    → (X : Var Γ → Bool)
    → all-local-max X ≡ true
    → PsSel Γps

  -- Extension case of reification.
  reify-pssel-ext :
    ∀ {Δ} {Γps : CtxPs Δ} (xps : VarPs Δ Γps)
    → (X : Var (ext-ctx xps) → Bool)
    → all-local-max X ≡ true
    → PsSel (ps-ext xps)

  -- Reification branches on whether the newest edge is selected.
  reify-pssel-ext-branch :
    ∀ {Δ} {Γps : CtxPs Δ} (xps : VarPs Δ Γps)
    → (X : Var (ext-ctx xps) → Bool)
    → (lm : all-local-max X ≡ true)
    → (b : Bool)
    → X vz ≡ b
    → PsSel (ps-ext xps)

  -- Evaluating a reified selector recovers the original raw selector.
  eval-reify-pssel :
    ∀ {Γ} (Γps : CtxPs Γ)
    → (X : Var Γ → Bool)
    → (lm : all-local-max X ≡ true)
    → (x : Var Γ)
    → eval-ps-sel (reify-pssel Γps X lm) x ≡ X x

  -- Extension case of the same correctness statement.
  eval-reify-pssel-ext :
    ∀ {Δ} {Γps : CtxPs Δ} (xps : VarPs Δ Γps)
    → (X : Var (ext-ctx xps) → Bool)
    → (lm : all-local-max X ≡ true)
    → (x : Var (ext-ctx xps))
    → eval-ps-sel (reify-pssel-ext xps X lm) x ≡ X x

  reify-pssel ps-ob X lm with X vz
  ... | false = pssel-ob-unsplit
  ... | true = pssel-ob-split
  reify-pssel (ps-ext xps) X lm = reify-pssel-ext xps X lm

  reify-pssel-ext xps X lm = reify-pssel-ext-branch xps X lm (X vz) refl

  -- If `f` is not selected, the reified selector is `unsplitSel` built from
  -- the recursively reified selector on the base context.
  reify-pssel-ext-branch {Δ} {Γps} xps X lm false eqX = unsplitSel s0 lmX notSel
    where
      X0 : Var Δ → Bool
      X0 = ext-base-selector xps X

      lm0 : all-local-max X0 ≡ true
      lm0 = ext-base-selector-local-max xps X lm

      s0 : PsSel Γps
      s0 = reify-pssel Γps X0 lm0

      notSel : eval-ps-sel s0 (varps-to-var xps) ≡ false
      notSel =
        trans
          (eval-reify-pssel Γps X0 lm0 (varps-to-var xps))
          (ext-base-selector-dangling-not-selected xps X lm)

      evalX :
        (y : Var (ext-ctx xps))
        → eval-step-unsplit {xps = xps} s0 y ≡ X y
      evalX vz = sym eqX
      evalX (vs vz) = sym (target-not-selected xps X lm)
      evalX (vs (vs y)) = eval-reify-pssel Γps X0 lm0 y

      lmX : all-local-max (eval-step-unsplit {xps = xps} s0) ≡ true
      lmX = trans (all-local-max-cong _ _ evalX) lm

  -- If `f` is selected, we produce the split constructor instead.
  reify-pssel-ext-branch {Δ} {Γps} xps X lm true eqX = splitSel s0 lmX notSel
    where
      X0 : Var Δ → Bool
      X0 = ext-base-selector xps X

      lm0 : all-local-max X0 ≡ true
      lm0 = ext-base-selector-local-max xps X lm

      s0 : PsSel Γps
      s0 = reify-pssel Γps X0 lm0

      notSel : eval-ps-sel s0 (varps-to-var xps) ≡ false
      notSel =
        trans
          (eval-reify-pssel Γps X0 lm0 (varps-to-var xps))
          (ext-base-selector-dangling-not-selected xps X lm)

      evalX :
        (y : Var (ext-ctx xps))
        → eval-step-split {xps = xps} s0 y ≡ X y
      evalX vz = sym eqX
      evalX (vs vz) = sym (target-not-selected xps X lm)
      evalX (vs (vs y)) = eval-reify-pssel Γps X0 lm0 y

      lmX : all-local-max (eval-step-split {xps = xps} s0) ≡ true
      lmX = trans (all-local-max-cong _ _ evalX) lm

  eval-reify-pssel ps-ob X lm vz with X vz
  ... | false = refl
  ... | true = refl
  eval-reify-pssel (ps-ext xps) X lm x = eval-reify-pssel-ext xps X lm x

  -- Correctness is proved by repeating the same branch analysis used in reification itself.
  eval-reify-pssel-ext {Δ} {Γps} xps X lm x = step (X vz) refl x
    where
      X0 : Var Δ → Bool
      X0 = ext-base-selector xps X

      lm0 : all-local-max X0 ≡ true
      lm0 = ext-base-selector-local-max xps X lm

      s0 : PsSel Γps
      s0 = reify-pssel Γps X0 lm0

      step :
        (b : Bool)
        → (eqX : X vz ≡ b)
        → (x : Var (ext-ctx xps))
        → eval-ps-sel (reify-pssel-ext-branch xps X lm b eqX) x ≡ X x
      step false eqX vz = sym eqX
      step false eqX (vs vz) = sym (target-not-selected xps X lm)
      step false eqX (vs (vs y)) = eval-reify-pssel Γps X0 lm0 y
      step true eqX vz = sym eqX
      step true eqX (vs vz) = sym (target-not-selected xps X lm)
      step true eqX (vs (vs y)) = eval-reify-pssel Γps X0 lm0 y

abstract
  reify-selector-cong-up :
    ∀ {Γ} (Γps : CtxPs Γ)
    → (X : Var Γ → Bool)
    → (lm : all-local-max X ≡ true)
    → Γ ↑ eval-ps-sel (reify-pssel Γps X lm) ≡ Γ ↑ X
  reify-selector-cong-up {Γ} Γps X lm =
    selector-cong-up Γ (eval-ps-sel (reify-pssel Γps X lm)) X
      (eval-reify-pssel Γps X lm)

  reify-selector-cong-in⁻ :
    ∀ {Γ} (Γps : CtxPs Γ)
    → (X : Var Γ → Bool)
    → (lm : all-local-max X ≡ true)
    → subst (λ Δ → Sub Δ Γ) (reify-selector-cong-up Γps X lm)
        (in⁻ Γ (eval-ps-sel (reify-pssel Γps X lm)))
      ≡ in⁻ Γ X
  reify-selector-cong-in⁻ {Γ} Γps X lm =
    selector-cong-in⁻ Γ (eval-ps-sel (reify-pssel Γps X lm)) X
      (eval-reify-pssel Γps X lm)

  reify-selector-cong-in⁺ :
    ∀ {Γ} (Γps : CtxPs Γ)
    → (X : Var Γ → Bool)
    → (lm : all-local-max X ≡ true)
    → subst (λ Δ → Sub Δ Γ) (reify-selector-cong-up Γps X lm)
        (in⁺ Γ (eval-ps-sel (reify-pssel Γps X lm))
          (pssel-local-max (reify-pssel Γps X lm)))
      ≡ in⁺ Γ X lm
  reify-selector-cong-in⁺ {Γ} Γps X lm =
    selector-cong-in⁺ Γ (eval-ps-sel (reify-pssel Γps X lm)) X
      (eval-reify-pssel Γps X lm)
      (pssel-local-max (reify-pssel Γps X lm))
      lm

func-pasting-raw :
  ∀ {Γ} (Γps : CtxPs Γ)
  → (X : Var Γ → Bool)
  → all-local-max X ≡ true
  → CtxPs (Γ ↑ X)
func-pasting-raw Γps X lm =
  subst CtxPs (reify-selector-cong-up Γps X lm) (func-pasting Γps (reify-pssel Γps X lm))

func-dangling-raw :
  ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
  → (X : Var Γ → Bool)
  → (lm : all-local-max X ≡ true)
  → VarPs (Γ ↑ X) (func-pasting-raw Γps X lm)
func-dangling-raw {Γps = Γps} xps X lm =
  transport-VarPs (reify-selector-cong-up Γps X lm)
    (func-dangling xps (reify-pssel Γps X lm))

abstract
  func-dangling-type-raw :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (X : Var Γ → Bool)
    → (lm : all-local-max X ≡ true)
    → varps-to-type (func-dangling-raw xps X lm)
      ≡ varps-to-type xps [ in⁻ Γ X ]T
  func-dangling-type-raw {Γps = Γps} xps X lm =
    trans
      (varps-to-type-transport (reify-selector-cong-up Γps X lm)
        (func-dangling xps (reify-pssel Γps X lm)))
      (trans
        (cong (subst Ty (reify-selector-cong-up Γps X lm))
          (func-dangling-type xps (reify-pssel Γps X lm)))
        (subst-[]T (reify-selector-cong-up Γps X lm) (reify-selector-cong-in⁻ Γps X lm)))

  func-dangling-var-raw :
    ∀ {Γ} {Γps : CtxPs Γ} (xps : VarPs Γ Γps)
    → (X : Var Γ → Bool)
    → (lm : all-local-max X ≡ true)
    → (notSel : X (varps-to-var xps) ≡ false)
    → var (varps-to-var xps) [ in⁻ Γ X ]t
      ≡ var (varps-to-var (func-dangling-raw xps X lm))
  func-dangling-var-raw {Γps = Γps} xps X lm notSel =
    trans
      (sym
        (subst-[]t
          {t = var (varps-to-var xps)}
          (reify-selector-cong-up Γps X lm)
          (reify-selector-cong-in⁻ Γps X lm)))
      (trans
        (cong (subst Tm (reify-selector-cong-up Γps X lm))
          (func-dangling-var xps (reify-pssel Γps X lm) notSel'))
        (trans
          (subst-var-transport (reify-selector-cong-up Γps X lm)
            (varps-to-var (func-dangling xps (reify-pssel Γps X lm))))
          (cong var
            (sym
              (varps-to-var-transport (reify-selector-cong-up Γps X lm)
                (func-dangling xps (reify-pssel Γps X lm)))))))
    where
      notSel' :
        eval-ps-sel (reify-pssel Γps X lm) (varps-to-var xps) ≡ false
      notSel' =
        trans
          (eval-reify-pssel Γps X lm (varps-to-var xps))
          notSel
```

## Test Cases

```agda
private
    arrow-ctx : Ctx
    arrow-ctx = ((∅ , ⋆) , ⋆) , ([ ⋆ ] var (vs vz) ⇒ var vz)
  
    var-f : Var arrow-ctx
    var-f = vz
  
    var-y : Var arrow-ctx
    var-y = vs vz
  
    var-x : Var arrow-ctx
    var-x = vs (vs vz)
  
    test-f-local-max : is-local-max {Γ = arrow-ctx} var-f ≡ true
    test-f-local-max = refl
  
    test-y-not-local-max : is-local-max {Γ = arrow-ctx} var-y ≡ false
    test-y-not-local-max = refl
  
    test-x-not-local-max : is-local-max {Γ = arrow-ctx} var-x ≡ false
    test-x-not-local-max = refl
  
    only-f : Var arrow-ctx → Bool
    only-f v = var-eq v var-f
  
    test-f-set-local-max : all-local-max only-f ≡ true
    test-f-set-local-max = refl
  
    test-func-ob : ((∅ , ⋆) ↑ (λ _ → true)) ≡ ((∅ , ⋆) , ⋆) , ([ ⋆ ] var (vs vz) ⇒ var vz)
    test-func-ob = refl
  
    test-func-ob-empty : ((∅ , ⋆) ↑ (λ _ → false)) ≡ (∅ , ⋆)
    test-func-ob-empty = refl
```



