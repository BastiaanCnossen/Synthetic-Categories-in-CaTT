# 1g-FunctorialityFull: Functoriality Preserves Fullness

This file records the next raw preCaTT target after
`1f-FunctorialityPasting`. We do not yet formalize the type-level operation
`A ↑ X` itself. Instead we state directly the raw hom-type that will later be
identified with the functoriality of a hom-type in the depth-0 case.

## Statement

Let `Γ` be a pasting context, let `A = [ A' ] u ⇒ v` be a hom-type over `Γ`,
and let `X : Var Γ → Bool` be a selector of maximal-dimension variables
such that `A` does not depend on `X`. Then in the functoriality context `Γ ↑ X` we
consider the raw coherence endpoints

- `coh-raw A' u v (in⁻ Γ X)`
- `coh-raw A' u v (in⁺ Γ X lm)`

and claim that the displayed type

- `[ A' ] coh-raw A' u v (in⁻ Γ X) ⇒ coh-raw A' u v (in⁺ Γ X lm)`

is again full.

We first show that in a pasting context, maximal-dimension variables are
automatically locally maximal. This lets us recover the local-maximality proof
needed by `reify-pssel`, `func-pasting-raw`, and `in⁺` internally, so the main
statements below only mention the maximal-dimension hypothesis.

```agda
module 1g-FunctorialityFull where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; subst)
open import Data.Bool.Base using (Bool; true; false; T; not; _∧_; _∨_)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (suc; _≤_; _<_; s≤s)
open import Data.Nat.Properties
  using (≡ᵇ⇒≡; ≤-refl; ≤-trans; <⇒≤; n≤1+n; 1+n≰n)
open import 0a-Logic
  using
    ( _iff_
    ; iff-refl
    ; true≠false
    ; false→not-true
    ; true→not-false
    ; ∧-true-intro
    ; ∨-true-introˡ
    ; ∨-true-introʳ
    ; ∨-trueʳ-from-falseˡ
    )
open import 1a-preCaTT
open import 1b-Dep
open import 1c-Pasting
open import 1d-Fullness
open import 1e-FunctorialityContexts
open import 1f-FunctorialityPasting
```

## Maximal vs Local Maximality

The key bridge is a dimension/dependency statement for variable declarations in
pasting contexts: if a variable occurs in the declared type of another
variable, then its dimension is strictly smaller. Therefore a variable whose
dimension already reaches `dim-ctx Γ` cannot occur in any declared type, so it
is locally maximal. We record that bridge as a postulate for now, and then lift
it from variables to selectors.

```agda
postulate
  max-dim-var-implies-local-max :
    ∀ {Γ}
    → (Γps : CtxPs Γ)
    → (x : Var Γ)
    → is-max-dim x ≡ true
    → is-local-max x ≡ true

abstract
  all-max-dim-implies-all-local-max :
    ∀ {Γ}
    → (Γps : CtxPs Γ)
    → (X : Var Γ → Bool)
    → all-max-dim X ≡ true
    → all-local-max X ≡ true
  all-max-dim-implies-all-local-max {Γ} Γps X max =
    ∀-var-map-true step max
    where
      step :
        (x : Var Γ)
        → (not (X x) ∨ is-max-dim x) ≡ true
        → (not (X x) ∨ is-local-max x) ≡ true
      step x p with X x in eqX
      ... | false = refl
      ... | true rewrite eqX =
        ∨-true-introʳ (max-dim-var-implies-local-max Γps x p)

in⁺-max :
  ∀ {Γ}
  → (Γps : CtxPs Γ)
  → (X : Var Γ → Bool)
  → all-max-dim X ≡ true
  → Sub (Γ ↑ X) Γ
in⁺-max {Γ} Γps X max =
  in⁺ Γ X (all-max-dim-implies-all-local-max Γps X max)

func-pasting-max :
  ∀ {Γ}
  → (Γps : CtxPs Γ)
  → (X : Var Γ → Bool)
  → all-max-dim X ≡ true
  → CtxPs (Γ ↑ X)
func-pasting-max Γps X max =
  func-pasting-raw Γps X (all-max-dim-implies-all-local-max Γps X max)
```

## Boundary Preservation

We prove the raw boundary statements in two stages.

First, we work with a structured selector `s : PsSel Γps`. This is still the
right induction principle: the recursive branch information is constructor-headed
there, whereas a raw boolean selector is not. So the real proof obligations are
recorded below at the `PsSel` level. The geometric content is that every
selected variable has maximal dimension in `Γ`; this is what rules out the
earlier counterexamples coming from selecting lower-dimensional boundary data.

Second, for a raw selector `X` we reify it to `reify-pssel Γps X lm`, apply the
structured statement, and transport back along
`reify-selector-cong-up`, `reify-selector-cong-in⁻`, and
`reify-selector-cong-in⁺`. The small transport lemmas from `1b-Dep` and
`1d-Fullness` are exactly what makes that last step direct. The local-maximality
proof `lm` used here is now synthesized from `all-max-dim X ≡ true`.

```agda
postulate
  functoriality-preserves-src-boundary-pssel :
    ∀ {Γ} (Γps : CtxPs Γ)
    → (s : PsSel Γps)
    → all-max-dim (eval-ps-sel s) ≡ true
    → (x : Var (Γ ↑ eval-ps-sel s))
    → in-src-bdry (func-pasting Γps s) x
      ≡ depends-on-var-sub x (in⁻ Γ (eval-ps-sel s))

  functoriality-preserves-tgt-boundary-pssel :
    ∀ {Γ} (Γps : CtxPs Γ)
    → (s : PsSel Γps)
    → all-max-dim (eval-ps-sel s) ≡ true
    → (x : Var (Γ ↑ eval-ps-sel s))
    → in-tgt-bdry (func-pasting Γps s) x
      ≡ depends-on-var-sub x (in⁺ Γ (eval-ps-sel s) (pssel-local-max s))

abstract
  functoriality-preserves-src-boundary :
    ∀ {Γ}
    → (Γps : CtxPs Γ)
    → (X : Var Γ → Bool)
    → (max : all-max-dim X ≡ true)
    → (x : Var (Γ ↑ X))
    → in-src-bdry (func-pasting-max Γps X max) x
      ≡ depends-on-var-sub x (in⁻ Γ X)
  functoriality-preserves-src-boundary {Γ} Γps X max x =
    trans
      (in-src-bdry-transport e x)
      (trans
        (functoriality-preserves-src-boundary-pssel Γps s max' x')
        (depends-on-var-sub-transport e x (reify-selector-cong-in⁻ Γps X lm)))
    where
      lm : all-local-max X ≡ true
      lm = all-max-dim-implies-all-local-max Γps X max

      s : PsSel Γps
      s = reify-pssel Γps X lm

      max' : all-max-dim (eval-ps-sel s) ≡ true
      max' = trans (all-max-dim-cong _ _ (eval-reify-pssel Γps X lm)) max

      e : (Γ ↑ eval-ps-sel s) ≡ (Γ ↑ X)
      e = reify-selector-cong-up Γps X lm

      x' : Var (Γ ↑ eval-ps-sel s)
      x' = subst Var (sym e) x

  functoriality-preserves-tgt-boundary :
    ∀ {Γ}
    → (Γps : CtxPs Γ)
    → (X : Var Γ → Bool)
    → (max : all-max-dim X ≡ true)
    → (x : Var (Γ ↑ X))
    → in-tgt-bdry (func-pasting-max Γps X max) x
      ≡ depends-on-var-sub x (in⁺-max Γps X max)
  functoriality-preserves-tgt-boundary {Γ} Γps X max x =
    trans
      (in-tgt-bdry-transport e x)
      (trans
        (functoriality-preserves-tgt-boundary-pssel Γps s max' x')
        (depends-on-var-sub-transport e x (reify-selector-cong-in⁺ Γps X lm)))
    where
      lm : all-local-max X ≡ true
      lm = all-max-dim-implies-all-local-max Γps X max

      s : PsSel Γps
      s = reify-pssel Γps X lm

      max' : all-max-dim (eval-ps-sel s) ≡ true
      max' = trans (all-max-dim-cong _ _ (eval-reify-pssel Γps X lm)) max

      e : (Γ ↑ eval-ps-sel s) ≡ (Γ ↑ X)
      e = reify-selector-cong-up Γps X lm

      x' : Var (Γ ↑ eval-ps-sel s)
      x' = subst Var (sym e) x
```

## Fullness Preservation

Once the raw source and target boundary lemmas are available, the fullness
argument is short. We name the two raw coherence endpoints, check the `COMP`
condition pointwise using the boundary equalities, and then conclude `is-full`
by left injection into the disjunction.

```agda
-- The two raw coherence endpoints that will later be identified with the
-- source and target of the functoriality type of a hom-type.
coh-in⁻ :
  ∀ {Γ}
  → (A : Ty Γ)
  → (u v : Tm Γ)
  → (X : Var Γ → Bool)
  → Tm (Γ ↑ X)
coh-in⁻ {Γ} A u v X = coh-raw A u v (in⁻ Γ X)

coh-in⁺ :
  ∀ {Γ}
  → (Γps : CtxPs Γ)
  → (A : Ty Γ)
  → (u v : Tm Γ)
  → (X : Var Γ → Bool)
  → all-max-dim X ≡ true
  → Tm (Γ ↑ X)
coh-in⁺ {Γ} Γps A u v X max = coh-raw A u v (in⁺-max Γps X max)

abstract
  -- Once the source/target boundaries of the functoriality context are known,
  -- the displayed raw coherence type satisfies COMP immediately.
  coh-inclusions-full-COMP :
    ∀ {Γ}
    → (Γps : CtxPs Γ)
    → (A' : Ty Γ)
    → (u v : Tm Γ)
    → (X : Var Γ → Bool)
    → (max : all-max-dim X ≡ true)
    → check-COMP
        (func-pasting-max Γps X max)
        (coh-in⁻ A' u v X)
        (coh-in⁺ Γps A' u v X max)
      ≡ true
  coh-inclusions-full-COMP {Γ} Γps A' u v X max =
    ∀-var-map-true
      {Γ = Γ ↑ X}
      {P = λ _ → true}
      step
      (∀-var-const-true {Γ = Γ ↑ X})
    where
      step :
        (x : Var (Γ ↑ X))
        → true ≡ true
        → ((depends-on-var-tm x (coh-in⁻ A' u v X)
              iff in-src-bdry (func-pasting-max Γps X max) x)
           ∧
           (depends-on-var-tm x (coh-in⁺ Γps A' u v X max)
              iff in-tgt-bdry (func-pasting-max Γps X max) x))
          ≡ true
      step x _ rewrite functoriality-preserves-src-boundary Γps X max x
                      | functoriality-preserves-tgt-boundary Γps X max x
        = ∧-true-intro
            {b = depends-on-var-sub x (in⁻ Γ X) iff depends-on-var-sub x (in⁻ Γ X)}
            {c = depends-on-var-sub x (in⁺-max Γps X max) iff depends-on-var-sub x (in⁺-max Γps X max)}
            iff-refl
            iff-refl

  -- The main raw fullness statement follows from the boundary lemma alone.
  functoriality-preserves-fullness :
    ∀ {Γ}
    → (Γps : CtxPs Γ)
    → (A' : Ty Γ)
    → (u v : Tm Γ)
    → (X : Var Γ → Bool)
    → (max : all-max-dim X ≡ true)
    → depends-on-X-ty X ([ A' ] u ⇒ v) ≡ false
    → is-full
        (func-pasting-max Γps X max)
        (coh-in⁻ A' u v X)
        (coh-in⁺ Γps A' u v X max)
      ≡ true
  functoriality-preserves-fullness Γps A' u v X max _ =
    ∨-true-introˡ (coh-inclusions-full-COMP Γps A' u v X max)
```
