# 2z-Extensionality: Well-formedness UIP and extensionality

This companion to `2a-CaTT` collects the **uniqueness** and **extensionality**
results for the intrinsic CaTT syntax, kept separate from the core definitions in
`2a-CaTT` itself.

Well-formedness proofs are unique (`*-iswf-uip`), which means that two terms
with the same raw part are equal (`Ty-ext`, `Tm-ext`, `Sub-ext`). The uniqueness
proofs are declared `abstract` for performance and `{-# TERMINATING #-}` because
the mutual recursion through `coh-wf` is not structurally decreasing to Agda's
termination checker. The pasting-context component of `coh-wf` is discharged by
the now-proven `Uniq.IsPsCtx-uip` (from `1z-Uniqueness`); the fullness component
still relies on the postulate `Full-uip` (which, as documented at the postulate,
is not provable as stated). Because the two `coh-wf` proofs may carry different
pasting-dimension indices `k`, the coh case first unifies them via
`Uniq.isPsCtx-dim-unique` before applying UIP.

The `abstract` UIP block and the `Ty-ext` / `Tm-ext` / `Sub-ext` lemmas must live
in the same module: the extensionality proofs `rewrite` by the abstract
`*-iswf-uip` witnesses, which is only transparent within the defining module.
The typed `hasTy-unique` is included here as well, since it is the only consumer
of `Ty-ext` outside this material.

```agda
module 2z-Extensionality where

import 1a-RawSyntax as Raw
import 1z-Uniqueness as Uniq

open import 2a-CaTT
open Raw using (RawCtx; RawTy; RawTm; RawSub; RawVar)

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## Well-formedness UIP

```agda
abstract
  {-# TERMINATING #-}
  mutual
    uip : ∀ {ℓ} {A : Set ℓ} {x y : A} (p q : x ≡ y) → p ≡ q
    uip refl refl = refl

    Ctx-iswf-uip : (Γ : RawCtx) → (p q : Ctx-iswf Γ) → p ≡ q
    Ty-iswf-uip  : {Γ : RawCtx} (A : RawTy Γ) → (p q : Ty-iswf A) → p ≡ q
    Tm-iswf-uip  : {Γ : RawCtx} (t : RawTm Γ) → (p q : Tm-iswf t) → p ≡ q
    Sub-iswf-uip : {Γ Δ : RawCtx} (σ : RawSub Γ Δ) → (p q : Sub-iswf σ) → p ≡ q

    Ctx-iswf-uip Raw.◆        ◆wf ◆wf = refl
    Ctx-iswf-uip (_ Raw.▸ _) (Γwf ▸wf (mkTyR _ Awf)) (Γwf' ▸wf (mkTyR _ Awf'))
      rewrite Ctx-iswf-uip _ Γwf Γwf' | Ty-iswf-uip _ Awf Awf' = refl

    Ty-iswf-uip Raw.⋆ ⋆wf ⋆wf = refl
    Ty-iswf-uip (Raw.[ A ] t ⇒ u)
      (hom-wf (mkTyR .A Awf)  {mkTmR .t twf}  {mkTmR .u uwf}  p  q)
      (hom-wf (mkTyR .A Awf') {mkTmR .t twf'} {mkTmR .u uwf'} p' q')
      rewrite Ty-iswf-uip A Awf Awf' | Tm-iswf-uip t twf twf'
            | Tm-iswf-uip u uwf uwf'
            | Uniq.HasTy-uip p p' | Uniq.HasTy-uip q q' = refl

    Tm-iswf-uip (Raw.var x) (var-wf .x) (var-wf .x) = refl
    Tm-iswf-uip (Raw.coh A t u σ)
      (coh-wf {Δ = Δ}  ps  Δwf  tA  tu  tv  p  q  r  σR)
      (coh-wf {Δ = .Δ} ps' Δwf' tA' tu' tv' p' q' r' σR')
      with Uniq.isPsCtx-dim-unique ps ps'
    ... | refl
      rewrite Ctx-iswf-uip Δ Δwf Δwf'
            | Ty-iswf-uip (Raw-TyR tA) (TyR-wf tA) (TyR-wf tA')
            | Tm-iswf-uip (Raw-TmR tu) (TmR-wf tu) (TmR-wf tu')
            | Tm-iswf-uip (Raw-TmR tv) (TmR-wf tv) (TmR-wf tv')
            | Uniq.HasTy-uip p p' | Uniq.HasTy-uip q q'
            | Uniq.IsPsCtx-uip ps ps' | Full-uip r r'
            | Sub-iswf-uip (Raw-SubR σR) (SubR-wf σR) (SubR-wf σR')
            = refl

    Sub-iswf-uip Raw.◆S ◆Swf ◆Swf = refl
    Sub-iswf-uip Raw.⟨ σ , t ⟩
      (⟨_,_⟩:[_]wf {A = mkTyR _ Awf}  (mkSubR .σ σwf)  (mkTmR .t twf)  r)
      (⟨_,_⟩:[_]wf {A = mkTyR _ Awf'} (mkSubR .σ σwf') (mkTmR .t twf') r')
      rewrite Ty-iswf-uip _ Awf Awf'
            | Sub-iswf-uip σ σwf σwf'
            | Tm-iswf-uip t twf twf'
            | Uniq.HasTySub-uip r r' = refl

    postulate
      -- `Full-uip` stays postulated, and (unlike `IsPsCtx-uip`) cannot simply be
      -- discharged by a structural induction, for two independent reasons:
      --   (1) `Full` is a genuine 5-way sum whose cases can overlap — e.g. over
      --       the object pasting context, `Full isps-ob ⋆ (var zero) (var zero)`
      --       is inhabited by BOTH `full-COMP` and `full-COMPCOH` (the boundary
      --       is the whole context), and these differ as data, so UIP is false.
      --   (2) the payloads (`COMP`, `INV`, …) are Π-types into `↔`-records, whose
      --       UIP would require function extensionality, which this development
      --       does not assume.
      -- The sound fix is to make the fullness component of `coh-wf` irrelevant
      -- rather than to prove this; see the discussion in `1z-Uniqueness`.
      Full-uip  : {Γ : RawCtx} {k : ℕ} {ps : P.IsPsCtx Γ k} {A : RawTy Γ} {u v : RawTm Γ}
        → (p q : Full ps A u v) → p ≡ q
```

## Extensionality

```agda
mutual
  Ty-ext : {Γ : Ctx} {A A' : Ty Γ} → Raw-Ty A ≡ Raw-Ty A' → A ≡ A'
  Tm-ext : {Γ : Ctx} {t t' : Tm Γ} → Raw-Tm t ≡ Raw-Tm t' → t ≡ t'
  Sub-ext : {Γ Δ : Ctx} {σ σ' : Sub Γ Δ} → Raw-Sub σ ≡ Raw-Sub σ' → σ ≡ σ'

  Ty-ext {A = mkTy A Awf} {mkTy .A Awf'} refl
    rewrite Ty-iswf-uip A Awf Awf' = refl
  Tm-ext {t = mkTm t twf} {mkTm .t twf'} refl
    rewrite Tm-iswf-uip t twf twf' = refl
  Sub-ext {σ = mkSub σ σwf} {mkSub .σ σwf'} refl
    rewrite Sub-iswf-uip σ σwf σwf' = refl
```

## Typed typing uniqueness

```agda
hasTy-unique : ∀ {Γ : Ctx} {t : Tm Γ} {A B : Ty Γ}
  → HasTy t A
  → HasTy t B
  → A ≡ B
hasTy-unique p q = Ty-ext (Uniq.hasTy-unique p q)
```
