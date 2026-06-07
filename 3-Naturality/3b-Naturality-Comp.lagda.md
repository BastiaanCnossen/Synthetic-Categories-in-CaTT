# 3b-Naturality-Comp: concrete naturality constructions

This is the computational companion to the relational core `3b-Naturality`.
The core defines the naturality relations. This module supplies the concrete
canonical operations where they are currently available.

Implemented here:

- suspended contexts `↑ctx`;
- endpoint substitutions `in⁻` and `in⁺`;
- extended suspended contexts `↑ctx-ext`;
- the ordinary substitution builder `↑sec-ext`;
- witnesses that the concrete contexts/endpoints satisfy `NatCtx`, `NatIn⁻`,
  `NatIn⁺`, and `NatCtxExt`.

Still postulated here:

- the naturality type `↑ty`;
- the naturality term/type pair `↑tm-ty`, `↑tm`;
- naturality of substitutions `↑sub`;
- the witnesses that `↑ty`, `↑tm`, and `↑sub` satisfy `NatTy`, `NatTm`, and
  `NatSub`.

Comparison sections are just `Sub` values, and their action
on a type is witnessed directly by `Raw.SubstTy`.

```agda
module 3b-Naturality-Comp where

open import 3b-Naturality public
open import 2a-CaTT-Comp
open import 3a-UpClosed-Comp

import 1a-RawSyntax-Comp as Raw
import 1b-Dependency as Dep

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; subst)
```

## Suspended contexts and endpoints

The definitions below are the context/endpoint fragment of the archived V10
construction. A selected snoc variable contributes the two endpoint variables and
one naturality variable; an unselected snoc contributes only one copied endpoint
variable.

```agda
mutual
  {-# TERMINATING #-}
  ↑ctx : (Γ : Ctx) → (X : Up Γ) → Ctx

  in⁻ : (Γ : Ctx) → (X : Up Γ) → Sub (↑ctx Γ X) Γ

  in⁺ : (Γ : Ctx) → (X : Up Γ) → Sub (↑ctx Γ X) Γ

  ↑ctx-ext : {Γ : Ctx} → (X : Up Γ) → (A : Ty Γ) → Ctx

  ↑ctx-ext-shape : {Γ : Ctx} → (X : Up Γ) → (A : Ty Γ) →
    ↑ctx-ext X A ≡ (((↑ctx Γ X) ▸ (A [ in⁻ Γ X ]T)) ▸ wkTy (A [ in⁺ Γ X ]T))

  postulate
    ↑ty : {Γ : Ctx} → (X : Up Γ) → (A : Ty Γ) → Ty (↑ctx-ext X A)

    ↑tm-ty : {Γ : Ctx} → (X : Up Γ) → Tm Γ → Ty (↑ctx Γ X)

    ↑tm : {Γ : Ctx} → (X : Up Γ) → (t : Tm Γ) → Tm (↑ctx Γ X)

    ↑sub : {Δ Γ : Ctx} → (X : Up Δ) → (σ : Sub Δ Γ) →
      Sub (↑ctx Δ X) (↑ctx Γ (inv-img σ X))

  in-ty-agree-unset :
    {Γ : Ctx} → (A : Ty Γ) →
    (X : Dep.SelVar (Raw-Ctx Γ)) → (X-up : is-upclosed X) →
    (indep : Dep.SelTypeIndep X (Raw-Ty A)) →
    A [ in⁻ Γ (mk X X-up) ]T ≡ A [ in⁺ Γ (mk X X-up) ]T

  ↑ctx Γ X with ctx-view Γ
  ... | ◆-view = ◆
  ... | ▸-view {Γ = Γ′} A with X
  ... | mk (Dep.sel-unset _ X) (snoc-unset .X X-up indep) =
    let
      X′ = mk X X-up
      ρ⁻ = in⁻ Γ′ X′
    in
    (↑ctx Γ′ X′) ▸ (A [ ρ⁻ ]T)
  ... | mk (Dep.sel-set _ X) (snoc-set .X X-up) =
    let
      X′ = mk X X-up
      ρ⁻ = in⁻ Γ′ X′
      ρ⁺ = in⁺ Γ′ X′
      A⁻ = A [ ρ⁻ ]T
      A⁺ = A [ ρ⁺ ]T
      A↑ = subst Ty (↑ctx-ext-shape X′ A) (↑ty X′ A)
    in
    (((↑ctx Γ′ X′) ▸ A⁻) ▸ wkTy A⁺) ▸ A↑

  in⁻ Γ X with ctx-view Γ
  ... | ◆-view = ◆S
  ... | ▸-view {Γ = Γ′} A with X
  ... | mk (Dep.sel-unset _ X) (snoc-unset .X X-up indep) =
    let
      X′ = mk X X-up
      ρ⁻ = in⁻ Γ′ X′
      A⁻ = A [ ρ⁻ ]T
      pzero : HasTySub (vz {A = A⁻}) A (wkSub {A = A⁻} ρ⁻)
      pzero =
        Raw.computed-hasTySub
          (subst (Raw.HasTy (Raw.var Raw.zero))
            (cong Raw-Ty (wkTy-[]T′ {A = A} {σ = ρ⁻} {B = A⁻}))
            (Raw.varTy (Raw.zeroTy (Raw.wkTy-rel _))))
    in
    ⟨ wkSub {A = A⁻} ρ⁻ , var Raw.zero ⟩:[ pzero ]
  ... | mk (Dep.sel-set _ X) (snoc-set .X X-up) =
    let
      X′ = mk X X-up
      ρ⁻ = in⁻ Γ′ X′
      ρ⁺ = in⁺ Γ′ X′
      A⁻ = A [ ρ⁻ ]T
      A⁺ = A [ ρ⁺ ]T
      A↑ = subst Ty (↑ctx-ext-shape X′ A) (↑ty X′ A)
      ρ⁻³ = wkSub {A = A↑} (wkSub {A = wkTy A⁺} (wkSub {A = A⁻} ρ⁻))
      px⁻ : HasTySub (var (Raw.succ (Raw.succ Raw.zero))) A ρ⁻³
      px⁻ =
        Raw.computed-hasTySub
          (subst (Raw.HasTy (Raw.var (Raw.succ (Raw.succ Raw.zero))))
            (cong Raw-Ty
              (wkTy³-[]T {A = A} {σ = ρ⁻} {B = A⁻} {C = wkTy A⁺} {D = A↑}))
            (Raw.varTy
              (Raw.succTy
                (Raw.succTy (Raw.zeroTy (Raw.wkTy-rel _)) (Raw.wkTy-rel _))
                (Raw.wkTy-rel _))))
    in
    ⟨ ρ⁻³ , var (Raw.succ (Raw.succ Raw.zero)) ⟩:[ px⁻ ]

  in⁺ Γ X with ctx-view Γ
  ... | ◆-view = ◆S
  ... | ▸-view {Γ = Γ′} A with X
  ... | mk (Dep.sel-unset _ X) (snoc-unset .X X-up indep) =
    let
      X′ = mk X X-up
      ρ⁺ = in⁺ Γ′ X′
      A⁻ = A [ in⁻ Γ′ X′ ]T
      eA = in-ty-agree-unset A X X-up indep
      pzero : HasTySub (vz {A = A⁻}) A (wkSub {A = A⁻} ρ⁺)
      pzero =
        Raw.computed-hasTySub
          (subst (Raw.HasTy (Raw.var Raw.zero))
            (trans
              (cong Raw.wkTy (cong Raw-Ty eA))
              (cong Raw-Ty (wkTy-[]T′ {A = A} {σ = ρ⁺} {B = A⁻})))
            (Raw.varTy (Raw.zeroTy (Raw.wkTy-rel _))))
    in
    ⟨ wkSub {A = A⁻} ρ⁺ , var Raw.zero ⟩:[ pzero ]
  ... | mk (Dep.sel-set _ X) (snoc-set .X X-up) =
    let
      X′ = mk X X-up
      ρ⁻ = in⁻ Γ′ X′
      ρ⁺ = in⁺ Γ′ X′
      A⁻ = A [ ρ⁻ ]T
      A⁺ = A [ ρ⁺ ]T
      A↑ = subst Ty (↑ctx-ext-shape X′ A) (↑ty X′ A)
      ρ⁺³ = wkSub {A = A↑} (wkSub {A = wkTy A⁺} (wkSub {A = A⁻} ρ⁺))
      px⁺ : HasTySub (var (Raw.succ Raw.zero)) A ρ⁺³
      px⁺ =
        Raw.computed-hasTySub
          (subst (Raw.HasTy (Raw.var (Raw.succ Raw.zero)))
            (cong Raw-Ty
              (wkTy³-[]T {A = A} {σ = ρ⁺} {B = A⁻} {C = wkTy A⁺} {D = A↑}))
            (Raw.varTy
              (Raw.succTy (Raw.zeroTy (Raw.wkTy-rel _)) (Raw.wkTy-rel _))))
    in
    ⟨ ρ⁺³ , var (Raw.succ Raw.zero) ⟩:[ px⁺ ]

  ↑ctx-ext {Γ} X A =
    let
      Γ↑ = ↑ctx Γ X
      A⁻ = A [ in⁻ Γ X ]T
      A⁺ = A [ in⁺ Γ X ]T
    in
    (Γ↑ ▸ A⁻) ▸ wkTy A⁺

  ↑ctx-ext-shape X A = refl

  in-var-agree-unset :
    {Γ : Ctx} →
    (X : Dep.SelVar (Raw-Ctx Γ)) → (X-up : is-upclosed X) →
    (x : Var Γ) → (Dep.selects X x → ⊥) →
    (var x) [ in⁻ Γ (mk X X-up) ]t
      ≡ (var x) [ in⁺ Γ (mk X X-up) ]t
  in-var-agree-unset {Γ = Γ} X X-up x nx with ctx-view Γ
  ... | ◆-view with x
  ... | ()
  in-var-agree-unset {Γ = Γ} X X-up x nx | ▸-view {Γ = Γ′} A with X | X-up | x | nx
  ... | Dep.sel-unset _ X | snoc-unset .X X-up indep | Raw.zero | nx =
    refl
  ... | Dep.sel-unset _ X | snoc-unset .X X-up indep | Raw.succ x | nx =
    let
      X′ = mk X X-up
      ρ⁻ = in⁻ Γ′ X′
      ρ⁺ = in⁺ Γ′ X′
      A⁻ = A [ ρ⁻ ]T
      ih = in-var-agree-unset X X-up x
            (λ sx → nx (Dep.there-unset sx))
    in
    trans
      (lookup-wkSub {A = A⁻} x ρ⁻)
      (trans
        (cong (_[ wk ]t) ih)
        (sym (lookup-wkSub {A = A⁻} x ρ⁺)))
  ... | Dep.sel-set _ X | snoc-set .X X-up | Raw.zero | nx =
    ⊥-elim (nx Dep.here)
  ... | Dep.sel-set _ X | snoc-set .X X-up | Raw.succ x | nx =
    let
      X′ = mk X X-up
      ρ⁻ = in⁻ Γ′ X′
      ρ⁺ = in⁺ Γ′ X′
      A⁻ = A [ ρ⁻ ]T
      A⁺ = A [ ρ⁺ ]T
      A↑ = subst Ty (↑ctx-ext-shape X′ A) (↑ty X′ A)
      ih = in-var-agree-unset X X-up x
            (λ sx → nx (Dep.there-set sx))
    in
    trans
      (lookup-wkSub³ {A = A⁻} {B = wkTy A⁺} {C = A↑} x ρ⁻)
      (trans
        (cong (_[ wk ]t) (cong (_[ wk ]t) (cong (_[ wk ]t) ih)))
        (sym (lookup-wkSub³ {A = A⁻} {B = wkTy A⁺} {C = A↑} x ρ⁺)))

  in-ty-agree-unset {Γ} A X X-up indep =
    sub-agree-ty A
      (in⁻ Γ (mk X X-up))
      (in⁺ Γ (mk X X-up))
      (λ x dx →
        in-var-agree-unset X X-up x
          (λ sx → indep sx dx))
```

## Relation witnesses for contexts and endpoints

```agda
mutual
  {-# TERMINATING #-}
  ↑ctx-NatCtx :
    (Γ : Ctx) → (X : Up Γ) → NatCtx Γ X (↑ctx Γ X)
  ↑ctx-NatCtx Γ X with ctx-view Γ | X
  ... | ◆-view | mk Dep.sel-base base = natctx-◆
  ... | ▸-view {Γ = Γ′} A | mk (Dep.sel-unset _ X) (snoc-unset .X X-up indep) =
    let
      X′ = mk X X-up
      nΓ = ↑ctx-NatCtx Γ′ X′
      ρ⁻ = in⁻ Γ′ X′
      nin⁻ = in⁻-NatIn⁻ Γ′ X′
      subA⁻ = Raw.substTy (Raw-Ty A) (Raw-Sub ρ⁻)
    in
    natctx-unset {indep = indep} nΓ nin⁻ subA⁻
  ... | ▸-view {Γ = Γ′} A | mk (Dep.sel-set _ X) (snoc-set .X X-up) =
    let
      X′ = mk X X-up
      nΓ = ↑ctx-NatCtx Γ′ X′
      ρ⁻ = in⁻ Γ′ X′
      ρ⁺ = in⁺ Γ′ X′
      A⁻ = A [ ρ⁻ ]T
      A⁺ = A [ ρ⁺ ]T
      A↑ = subst Ty (↑ctx-ext-shape X′ A) (↑ty X′ A)
      nin⁻ = in⁻-NatIn⁻ Γ′ X′
      nin⁺ = in⁺-NatIn⁺ Γ′ X′
      subA⁻ = Raw.substTy (Raw-Ty A) (Raw-Sub ρ⁻)
      subA⁺ = Raw.substTy (Raw-Ty A) (Raw-Sub ρ⁺)
      wkA⁺ = Raw.wkTy-rel (Raw-Ty A⁺)
    in
    natctx-set
      {A = A} {X = X} {X-up = X-up}
      {ρ⁻ = ρ⁻} {ρ⁺ = ρ⁺}
      {A⁻ = A⁻} {A⁺ = A⁺} {A⁺ʷ = wkTy A⁺} {A↑ = A↑}
      nΓ nin⁻ nin⁺ subA⁻ subA⁺ wkA⁺

  in⁻-NatIn⁻ :
    (Γ : Ctx) → (X : Up Γ) → NatIn⁻ X (↑ctx-NatCtx Γ X) (in⁻ Γ X)
  in⁻-NatIn⁻ Γ X with ctx-view Γ | X
  ... | ◆-view | mk Dep.sel-base base = natin⁻-◆
  ... | ▸-view {Γ = Γ′} A | mk (Dep.sel-unset _ X) (snoc-unset .X X-up indep) =
    let
      X′ = mk X X-up
      nΓ = ↑ctx-NatCtx Γ′ X′
      ρ⁻ = in⁻ Γ′ X′
      A⁻ = A [ ρ⁻ ]T
      nin⁻ = in⁻-NatIn⁻ Γ′ X′
      subA⁻ = Raw.substTy (Raw-Ty A) (Raw-Sub ρ⁻)
      wkρ⁻ = Raw.wkSub-rel (Raw-Sub ρ⁻)
      pzero : HasTySub (vz {A = A⁻}) A (wkSub {A = A⁻} ρ⁻)
      pzero =
        Raw.computed-hasTySub
          (subst (Raw.HasTy (Raw.var Raw.zero))
            (cong Raw-Ty (wkTy-[]T′ {A = A} {σ = ρ⁻} {B = A⁻}))
            (Raw.varTy (Raw.zeroTy (Raw.wkTy-rel _))))
    in
    natin⁻-unset {indep = indep} nΓ nin⁻ subA⁻ wkρ⁻ pzero
  ... | ▸-view {Γ = Γ′} A | mk (Dep.sel-set _ X) (snoc-set .X X-up) =
    let
      X′ = mk X X-up
      nΓ = ↑ctx-NatCtx Γ′ X′
      ρ⁻ = in⁻ Γ′ X′
      ρ⁺ = in⁺ Γ′ X′
      A⁻ = A [ ρ⁻ ]T
      A⁺ = A [ ρ⁺ ]T
      A↑ = subst Ty (↑ctx-ext-shape X′ A) (↑ty X′ A)
      ρ⁻¹ = wkSub {A = A⁻} ρ⁻
      ρ⁻² = wkSub {A = wkTy A⁺} ρ⁻¹
      ρ⁻³ = wkSub {A = A↑} ρ⁻²
      nin⁻ = in⁻-NatIn⁻ Γ′ X′
      nin⁺ = in⁺-NatIn⁺ Γ′ X′
      subA⁻ = Raw.substTy (Raw-Ty A) (Raw-Sub ρ⁻)
      subA⁺ = Raw.substTy (Raw-Ty A) (Raw-Sub ρ⁺)
      wkA⁺ = Raw.wkTy-rel (Raw-Ty A⁺)
      wkρ¹ = Raw.wkSub-rel (Raw-Sub ρ⁻)
      wkρ² = Raw.wkSub-rel (Raw-Sub ρ⁻¹)
      wkρ³ = Raw.wkSub-rel (Raw-Sub ρ⁻²)
      px⁻ : HasTySub (var (Raw.succ (Raw.succ Raw.zero))) A ρ⁻³
      px⁻ =
        Raw.computed-hasTySub
          (subst (Raw.HasTy (Raw.var (Raw.succ (Raw.succ Raw.zero))))
            (cong Raw-Ty
              (wkTy³-[]T {A = A} {σ = ρ⁻} {B = A⁻} {C = wkTy A⁺} {D = A↑}))
            (Raw.varTy
              (Raw.succTy
                (Raw.succTy (Raw.zeroTy (Raw.wkTy-rel _)) (Raw.wkTy-rel _))
                (Raw.wkTy-rel _))))
    in
    natin⁻-set
      {A = A} {X = X} {X-up = X-up}
      {ρ⁻ = ρ⁻} {ρ⁺ = ρ⁺}
      {A⁻ = A⁻} {A⁺ = A⁺} {A⁺ʷ = wkTy A⁺} {A↑ = A↑}
      {ρ⁻¹ = ρ⁻¹} {ρ⁻² = ρ⁻²} {ρ⁻³ = ρ⁻³}
      nΓ nin⁻ nin⁺ subA⁻ subA⁺ wkA⁺ wkρ¹ wkρ² wkρ³ px⁻

  in⁺-NatIn⁺ :
    (Γ : Ctx) → (X : Up Γ) → NatIn⁺ X (↑ctx-NatCtx Γ X) (in⁺ Γ X)
  in⁺-NatIn⁺ Γ X with ctx-view Γ | X
  ... | ◆-view | mk Dep.sel-base base = natin⁺-◆
  ... | ▸-view {Γ = Γ′} A | mk (Dep.sel-unset _ X) (snoc-unset .X X-up indep) =
    let
      X′ = mk X X-up
      nΓ = ↑ctx-NatCtx Γ′ X′
      ρ⁻ = in⁻ Γ′ X′
      ρ⁺ = in⁺ Γ′ X′
      A⁻ = A [ ρ⁻ ]T
      nin⁻ = in⁻-NatIn⁻ Γ′ X′
      nin⁺ = in⁺-NatIn⁺ Γ′ X′
      subA⁻ = Raw.substTy (Raw-Ty A) (Raw-Sub ρ⁻)
      wkρ⁺ = Raw.wkSub-rel (Raw-Sub ρ⁺)
      eA = in-ty-agree-unset A X X-up indep
      pzero : HasTySub (vz {A = A⁻}) A (wkSub {A = A⁻} ρ⁺)
      pzero =
        Raw.computed-hasTySub
          (subst (Raw.HasTy (Raw.var Raw.zero))
            (trans
              (cong Raw.wkTy (cong Raw-Ty eA))
              (cong Raw-Ty (wkTy-[]T′ {A = A} {σ = ρ⁺} {B = A⁻})))
            (Raw.varTy (Raw.zeroTy (Raw.wkTy-rel _))))
    in
    natin⁺-unset {indep = indep} nΓ nin⁻ nin⁺ subA⁻ wkρ⁺ pzero
  ... | ▸-view {Γ = Γ′} A | mk (Dep.sel-set _ X) (snoc-set .X X-up) =
    let
      X′ = mk X X-up
      nΓ = ↑ctx-NatCtx Γ′ X′
      ρ⁻ = in⁻ Γ′ X′
      ρ⁺ = in⁺ Γ′ X′
      A⁻ = A [ ρ⁻ ]T
      A⁺ = A [ ρ⁺ ]T
      A↑ = subst Ty (↑ctx-ext-shape X′ A) (↑ty X′ A)
      ρ⁺¹ = wkSub {A = A⁻} ρ⁺
      ρ⁺² = wkSub {A = wkTy A⁺} ρ⁺¹
      ρ⁺³ = wkSub {A = A↑} ρ⁺²
      nin⁻ = in⁻-NatIn⁻ Γ′ X′
      nin⁺ = in⁺-NatIn⁺ Γ′ X′
      subA⁻ = Raw.substTy (Raw-Ty A) (Raw-Sub ρ⁻)
      subA⁺ = Raw.substTy (Raw-Ty A) (Raw-Sub ρ⁺)
      wkA⁺ = Raw.wkTy-rel (Raw-Ty A⁺)
      wkρ¹ = Raw.wkSub-rel (Raw-Sub ρ⁺)
      wkρ² = Raw.wkSub-rel (Raw-Sub ρ⁺¹)
      wkρ³ = Raw.wkSub-rel (Raw-Sub ρ⁺²)
      px⁺ : HasTySub (var (Raw.succ Raw.zero)) A ρ⁺³
      px⁺ =
        Raw.computed-hasTySub
          (subst (Raw.HasTy (Raw.var (Raw.succ Raw.zero)))
            (cong Raw-Ty
              (wkTy³-[]T {A = A} {σ = ρ⁺} {B = A⁻} {C = wkTy A⁺} {D = A↑}))
            (Raw.varTy
              (Raw.succTy (Raw.zeroTy (Raw.wkTy-rel _)) (Raw.wkTy-rel _))))
    in
    natin⁺-set
      {A = A} {X = X} {X-up = X-up}
      {ρ⁻ = ρ⁻} {ρ⁺ = ρ⁺}
      {A⁻ = A⁻} {A⁺ = A⁺} {A⁺ʷ = wkTy A⁺} {A↑ = A↑}
      {ρ⁺¹ = ρ⁺¹} {ρ⁺² = ρ⁺²} {ρ⁺³ = ρ⁺³}
      nΓ nin⁻ nin⁺ subA⁻ subA⁺ wkA⁺ wkρ¹ wkρ² wkρ³ px⁺

↑ctx-ext-NatCtxExt :
  {Γ : Ctx} → (X : Up Γ) → (A : Ty Γ) →
  NatCtxExt X (↑ctx-NatCtx Γ X) A (↑ctx-ext X A)
↑ctx-ext-NatCtxExt {Γ} X A =
  let
    ρ⁻ = in⁻ Γ X
    ρ⁺ = in⁺ Γ X
    A⁻ = A [ ρ⁻ ]T
    A⁺ = A [ ρ⁺ ]T
  in
  natctx-ext
    {ρ⁻ = ρ⁻} {ρ⁺ = ρ⁺}
    {A⁻ = A⁻} {A⁺ = A⁺} {A⁺ʷ = wkTy A⁺}
    (in⁻-NatIn⁻ Γ X)
    (in⁺-NatIn⁺ Γ X)
    (Raw.substTy (Raw-Ty A) (Raw-Sub ρ⁻))
    (Raw.substTy (Raw-Ty A) (Raw-Sub ρ⁺))
    (Raw.wkTy-rel (Raw-Ty A⁺))
```

## Remaining satisfaction witnesses

These witnesses remain postulated because the corresponding operations are still
postulated.

```agda
postulate
  ↑ty-NatTy :
    {Γ : Ctx} → (X : Up Γ) → (A : Ty Γ) →
    NatTy X (↑ctx-NatCtx Γ X) A (↑ctx-ext-NatCtxExt X A) (↑ty X A)

  ↑tm-NatTm :
    {Γ : Ctx} → (X : Up Γ) → (t : Tm Γ) →
    NatTm X (↑ctx-NatCtx Γ X) t (↑tm-ty X t) (↑tm X t)

  ↑sub-NatSub :
    {Δ Γ : Ctx} → (X : Up Δ) → (σ : Sub Δ Γ) →
    NatSub X (↑ctx-NatCtx Δ X) σ
      (↑ctx-NatCtx Γ (inv-img σ X)) (↑sub X σ)
```

## Substitution-naturality of the naturality type

The naturality construction commutes with substitution. This is the one *basic
naturality fact* the higher diagram-hom layer needs in order to reindex hom
**types** along a context substitution, and it is postulated here in the same
abstract-interface spirit as `↑ty` / `↑ty-NatTy` themselves (the concrete `↑ty` is
still postulated, so its substitution behaviour is postulated too).

`↑sub-ext X σ A` is the action of `σ : Sub Δ Γ` on the *extended* suspended context:
it extends `↑sub X σ` across the two endpoint variables of `↑ctx-ext`. `↑ty-[]T` then
says that substituting the naturality type of an entry `A` (over `Γ`, with the
inverse-image selector) down to `Δ` yields the naturality type of the substituted
entry `A [ σ ]T`.

```agda
postulate
  ↑sub-ext :
    {Δ Γ : Ctx} → (X : Up Δ) → (σ : Sub Δ Γ) → (A : Ty Γ) →
    Sub (↑ctx-ext X (A [ σ ]T)) (↑ctx-ext (inv-img σ X) A)

  ↑ty-[]T :
    {Δ Γ : Ctx} → (X : Up Δ) → (σ : Sub Δ Γ) → (A : Ty Γ) →
    ↑ty (inv-img σ X) A [ ↑sub-ext X σ A ]T ≡ ↑ty X (A [ σ ]T)
```

## Extended comparison substitution

`↑sec-ext` extends an ordinary substitution `s : Sub Δ (↑ctx Γ X)` across the two
endpoint variables of `↑ctx-ext X A`. The endpoint type arguments may be any
types related to the computed endpoint substitutions by `Raw.SubstTy`; the
definition transports the supplied typing witnesses to the concrete computed
endpoint types before snocing.

```agda
↑sec-ext :
  {Γ Δ : Ctx} → (X : Up Γ) → (A : Ty Γ) →
  (s : Sub Δ (↑ctx Γ X)) →
  (t⁻ t⁺ : Tm Δ) →
  {A⁻ A⁺ : Ty (↑ctx Γ X)} →
  Raw.SubstTy (Raw-Ty A) (Raw-Sub (in⁻ Γ X)) (Raw-Ty A⁻) →
  Raw.SubstTy (Raw-Ty A) (Raw-Sub (in⁺ Γ X)) (Raw-Ty A⁺) →
  HasTySub t⁻ A⁻ s →
  HasTySub t⁺ A⁺ s →
  Sub Δ (↑ctx-ext X A)
↑sec-ext {Γ} {Δ} X A s t⁻ t⁺ {A⁻} {A⁺} subA⁻ subA⁺ p⁻ p⁺ =
  let
    A⁻₀ = A [ in⁻ Γ X ]T
    A⁺₀ = A [ in⁺ Γ X ]T

    e⁻ : A⁻₀ ≡ A⁻
    e⁻ = Ty-ext (Raw.substTy→[]T≡ subA⁻)

    e⁺ : A⁺₀ ≡ A⁺
    e⁺ = Ty-ext (Raw.substTy→[]T≡ subA⁺)

    p⁻₀ : HasTySub t⁻ A⁻₀ s
    p⁻₀ =
      hasTySub-conv
        {t = t⁻}
        {A = A⁻} {B = A⁻₀} {σ = s} {τ = s}
        p⁻
        (sym (cong (λ B → B [ s ]T) e⁻))

    σ⁻ : Sub Δ ((↑ctx Γ X) ▸ A⁻₀)
    σ⁻ = ⟨ s , t⁻ ⟩:[ p⁻₀ ]

    p⁺₀ : HasTySub t⁺ A⁺₀ s
    p⁺₀ =
      hasTySub-conv
        {t = t⁺}
        {A = A⁺} {B = A⁺₀} {σ = s} {τ = s}
        p⁺
        (sym (cong (λ B → B [ s ]T) e⁺))

    p⁺ʷ : HasTySub t⁺ (wkTy {A = A⁻₀} A⁺₀) σ⁻
    p⁺ʷ =
      hasTySub-conv
        {t = t⁺}
        {A = A⁺₀} {B = wkTy {A = A⁻₀} A⁺₀} {σ = s} {τ = σ⁻}
        p⁺₀
        (sym (wkTy-snoc-sub A⁺₀ s t⁻ {p = p⁻₀}))
  in
  ⟨ σ⁻ , t⁺ ⟩:[ p⁺ʷ ]
```
