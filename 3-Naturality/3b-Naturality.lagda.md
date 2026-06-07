# 3b-Naturality: relational naturality core

The **naturality construction** assigns, to a context `Γ` and an up-closed
selector `X : Up Γ`, a suspended context `Γ ↑ X` with two endpoint
substitutions

```text
in⁻ , in⁺ : Γ ↑ X → Γ.
```

For a type `Γ ⊢ A`, the construction also uses the extended suspended context

```text
Γ ↑ X , x⁻ : A[in⁻] , x⁺ : A[in⁺]
```

and a naturality type over it. Terms and substitutions then have corresponding
naturality data.

This file is the **relational core**. It does not compute the chosen suspended
context or endpoints; it recognizes them with proof-relevant relations. The
concrete functions (`↑ctx`, `in⁻`, `in⁺`, `↑ctx-ext`, `↑ty`, `↑tm`, `↑sub`,
`↑sec-ext`) live in `3b-Naturality-Comp`.

Comparison sections are ordinary substitutions into suspended contexts. There is
no separate section abstraction layer: downstream users should use `Sub`,
`Raw.SubstTy`, `Raw.SubstTm`, and `Raw.CompSub` directly.

Remaining postulates in this file are listed in the status section.

```agda
module 3b-Naturality where

open import Data.Empty using (⊥)

import 1a-RawSyntax as Raw
import 1b-Dependency as Dep
open import 2a-CaTT
open import 3a-UpClosed
```

## Auxiliary notions

`NoTmDep X t` says `t` depends on none of the variables selected by `X`.

```agda
NoTmDep : {Γ : Ctx} → Up Γ → Tm Γ → Set₁
NoTmDep X t = tm-dep X t → ⊥
```

`IteratedHom A B` witnesses that `B` is obtained from `A` by adding finitely many
hom-layers.

```agda
data IteratedHom : {Γ : Ctx} → Ty Γ → Ty Γ → Set₁ where
  ih-base :
    {Γ : Ctx} {A : Ty Γ} →
    IteratedHom A A

  ih-hom :
    {Γ : Ctx} {A B : Ty Γ} {t u : Tm Γ}
    {p : HasTy t B} {q : HasTy u B} →
    IteratedHom A B →
    IteratedHom A ([ B ] t ⇒ u :[ p , q ])

iterated-hom-drop :
  {Γ : Ctx} {A B : Ty Γ} {u v : Tm Γ}
  {p : HasTy u A} {q : HasTy v A} →
  IteratedHom ([ A ] u ⇒ v :[ p , q ]) B →
  IteratedHom A B
iterated-hom-drop ih-base = ih-hom ih-base
iterated-hom-drop (ih-hom pB) = ih-hom (iterated-hom-drop pB)
```

## Context and endpoint naturality

These four relations mirror the recursive shape of the archived implementation.
The unselected snoc case adds one endpoint variable. The selected snoc case adds
the two endpoint variables and then one naturality variable. Substitution and
weakening are recorded relationally through `Raw.SubstTy`, `Raw.WkTy`, and
`Raw.WkSub`; the core never calls computed substitution or weakening.

```agda
mutual
  data NatCtx : (Γ : Ctx) → Up Γ → Ctx → Set₁ where
    natctx-◆ :
      NatCtx ◆ (mk Dep.sel-base base) ◆

    natctx-unset :
      {Γ Γ↑ : Ctx} {A : Ty Γ}
      {X : Dep.SelVar (Raw-Ctx Γ)}
      {X-up : is-upclosed X}
      {indep : Dep.SelTypeIndep X (Raw-Ty A)}
      {ρ⁻ : Sub Γ↑ Γ} {A⁻ : Ty Γ↑} →
      (nΓ : NatCtx Γ (mk X X-up) Γ↑) →
      NatIn⁻ (mk X X-up) nΓ ρ⁻ →
      Raw.SubstTy (Raw-Ty A) (Raw-Sub ρ⁻) (Raw-Ty A⁻) →
      NatCtx (Γ ▸ A)
        (mk (Dep.sel-unset (Raw-Ty A) X) (snoc-unset X X-up indep))
        (Γ↑ ▸ A⁻)

    natctx-set :
      {Γ Γ↑ : Ctx} {A : Ty Γ}
      {X : Dep.SelVar (Raw-Ctx Γ)}
      {X-up : is-upclosed X}
      {ρ⁻ ρ⁺ : Sub Γ↑ Γ}
      {A⁻ A⁺ : Ty Γ↑}
      {A⁺ʷ : Ty (Γ↑ ▸ A⁻)}
      {A↑ : Ty ((Γ↑ ▸ A⁻) ▸ A⁺ʷ)} →
      (nΓ : NatCtx Γ (mk X X-up) Γ↑) →
      NatIn⁻ (mk X X-up) nΓ ρ⁻ →
      NatIn⁺ (mk X X-up) nΓ ρ⁺ →
      Raw.SubstTy (Raw-Ty A) (Raw-Sub ρ⁻) (Raw-Ty A⁻) →
      Raw.SubstTy (Raw-Ty A) (Raw-Sub ρ⁺) (Raw-Ty A⁺) →
      Raw.WkTy {A = Raw-Ty A⁻} (Raw-Ty A⁺) (Raw-Ty A⁺ʷ) →
      NatCtx (Γ ▸ A)
        (mk (Dep.sel-set (Raw-Ty A) X) (snoc-set X X-up))
        (((Γ↑ ▸ A⁻) ▸ A⁺ʷ) ▸ A↑)

  data NatCtxExt {Γ Γ↑ : Ctx}
      (X : Up Γ) (nΓ : NatCtx Γ X Γ↑) (A : Ty Γ) :
      Ctx → Set₁ where
    natctx-ext :
      {ρ⁻ ρ⁺ : Sub Γ↑ Γ}
      {A⁻ A⁺ : Ty Γ↑}
      {A⁺ʷ : Ty (Γ↑ ▸ A⁻)} →
      NatIn⁻ X nΓ ρ⁻ →
      NatIn⁺ X nΓ ρ⁺ →
      Raw.SubstTy (Raw-Ty A) (Raw-Sub ρ⁻) (Raw-Ty A⁻) →
      Raw.SubstTy (Raw-Ty A) (Raw-Sub ρ⁺) (Raw-Ty A⁺) →
      Raw.WkTy {A = Raw-Ty A⁻} (Raw-Ty A⁺) (Raw-Ty A⁺ʷ) →
      NatCtxExt X nΓ A ((Γ↑ ▸ A⁻) ▸ A⁺ʷ)

  data NatIn⁻ :
      {Γ Γ↑ : Ctx} →
      (X : Up Γ) (nΓ : NatCtx Γ X Γ↑) →
      Sub Γ↑ Γ → Set₁ where
    natin⁻-◆ :
      NatIn⁻ (mk Dep.sel-base base) natctx-◆ ◆S

    natin⁻-unset :
      {Γ Γ↑ : Ctx} {A : Ty Γ}
      {X : Dep.SelVar (Raw-Ctx Γ)}
      {X-up : is-upclosed X}
      {indep : Dep.SelTypeIndep X (Raw-Ty A)}
      {ρ⁻ : Sub Γ↑ Γ} {A⁻ : Ty Γ↑}
      {ρ⁻ʷ : Sub (Γ↑ ▸ A⁻) Γ} →
      (nΓ : NatCtx Γ (mk X X-up) Γ↑) →
      (nin⁻ : NatIn⁻ (mk X X-up) nΓ ρ⁻) →
      (subA⁻ : Raw.SubstTy (Raw-Ty A) (Raw-Sub ρ⁻) (Raw-Ty A⁻)) →
      Raw.WkSub {A = Raw-Ty A⁻} (Raw-Sub ρ⁻) (Raw-Sub ρ⁻ʷ) →
      (pzero : HasTySub (vz {Γ = Γ↑} {A = A⁻}) A ρ⁻ʷ) →
      NatIn⁻
        (mk (Dep.sel-unset (Raw-Ty A) X) (snoc-unset X X-up indep))
        (natctx-unset {indep = indep} nΓ nin⁻ subA⁻)
        (snocSubEq ρ⁻ʷ A (vz {Γ = Γ↑} {A = A⁻}) pzero)

    natin⁻-set :
      {Γ Γ↑ : Ctx} {A : Ty Γ}
      {X : Dep.SelVar (Raw-Ctx Γ)}
      {X-up : is-upclosed X}
      {ρ⁻ ρ⁺ : Sub Γ↑ Γ}
      {A⁻ A⁺ : Ty Γ↑}
      {A⁺ʷ : Ty (Γ↑ ▸ A⁻)}
      {A↑ : Ty ((Γ↑ ▸ A⁻) ▸ A⁺ʷ)}
      {ρ⁻¹ : Sub (Γ↑ ▸ A⁻) Γ}
      {ρ⁻² : Sub ((Γ↑ ▸ A⁻) ▸ A⁺ʷ) Γ}
      {ρ⁻³ : Sub (((Γ↑ ▸ A⁻) ▸ A⁺ʷ) ▸ A↑) Γ} →
      (nΓ : NatCtx Γ (mk X X-up) Γ↑) →
      (nin⁻ : NatIn⁻ (mk X X-up) nΓ ρ⁻) →
      (nin⁺ : NatIn⁺ (mk X X-up) nΓ ρ⁺) →
      (subA⁻ : Raw.SubstTy (Raw-Ty A) (Raw-Sub ρ⁻) (Raw-Ty A⁻)) →
      (subA⁺ : Raw.SubstTy (Raw-Ty A) (Raw-Sub ρ⁺) (Raw-Ty A⁺)) →
      (wkA⁺ : Raw.WkTy {A = Raw-Ty A⁻} (Raw-Ty A⁺) (Raw-Ty A⁺ʷ)) →
      Raw.WkSub {A = Raw-Ty A⁻} (Raw-Sub ρ⁻) (Raw-Sub ρ⁻¹) →
      Raw.WkSub {A = Raw-Ty A⁺ʷ} (Raw-Sub ρ⁻¹) (Raw-Sub ρ⁻²) →
      Raw.WkSub {A = Raw-Ty A↑} (Raw-Sub ρ⁻²) (Raw-Sub ρ⁻³) →
      (px⁻ : HasTySub
        (var {Γ = (((Γ↑ ▸ A⁻) ▸ A⁺ʷ) ▸ A↑)}
          (Raw.succ (Raw.succ Raw.zero)))
        A ρ⁻³) →
      NatIn⁻
        (mk (Dep.sel-set (Raw-Ty A) X) (snoc-set X X-up))
        (natctx-set
          {A = A} {X = X} {X-up = X-up}
          {ρ⁻ = ρ⁻} {ρ⁺ = ρ⁺}
          {A⁻ = A⁻} {A⁺ = A⁺} {A⁺ʷ = A⁺ʷ} {A↑ = A↑}
          nΓ nin⁻ nin⁺ subA⁻ subA⁺ wkA⁺)
        (snocSubEq ρ⁻³ A
          (var {Γ = (((Γ↑ ▸ A⁻) ▸ A⁺ʷ) ▸ A↑)}
            (Raw.succ (Raw.succ Raw.zero)))
          px⁻)

  data NatIn⁺ :
      {Γ Γ↑ : Ctx} →
      (X : Up Γ) (nΓ : NatCtx Γ X Γ↑) →
      Sub Γ↑ Γ → Set₁ where
    natin⁺-◆ :
      NatIn⁺ (mk Dep.sel-base base) natctx-◆ ◆S

    natin⁺-unset :
      {Γ Γ↑ : Ctx} {A : Ty Γ}
      {X : Dep.SelVar (Raw-Ctx Γ)}
      {X-up : is-upclosed X}
      {indep : Dep.SelTypeIndep X (Raw-Ty A)}
      {ρ⁻ ρ⁺ : Sub Γ↑ Γ} {A⁻ : Ty Γ↑}
      {ρ⁺ʷ : Sub (Γ↑ ▸ A⁻) Γ} →
      (nΓ : NatCtx Γ (mk X X-up) Γ↑) →
      (nin⁻ : NatIn⁻ (mk X X-up) nΓ ρ⁻) →
      (nin⁺ : NatIn⁺ (mk X X-up) nΓ ρ⁺) →
      (subA⁻ : Raw.SubstTy (Raw-Ty A) (Raw-Sub ρ⁻) (Raw-Ty A⁻)) →
      Raw.WkSub {A = Raw-Ty A⁻} (Raw-Sub ρ⁺) (Raw-Sub ρ⁺ʷ) →
      (pzero : HasTySub (vz {Γ = Γ↑} {A = A⁻}) A ρ⁺ʷ) →
      NatIn⁺
        (mk (Dep.sel-unset (Raw-Ty A) X) (snoc-unset X X-up indep))
        (natctx-unset {indep = indep} nΓ nin⁻ subA⁻)
        (snocSubEq ρ⁺ʷ A (vz {Γ = Γ↑} {A = A⁻}) pzero)

    natin⁺-set :
      {Γ Γ↑ : Ctx} {A : Ty Γ}
      {X : Dep.SelVar (Raw-Ctx Γ)}
      {X-up : is-upclosed X}
      {ρ⁻ ρ⁺ : Sub Γ↑ Γ}
      {A⁻ A⁺ : Ty Γ↑}
      {A⁺ʷ : Ty (Γ↑ ▸ A⁻)}
      {A↑ : Ty ((Γ↑ ▸ A⁻) ▸ A⁺ʷ)}
      {ρ⁺¹ : Sub (Γ↑ ▸ A⁻) Γ}
      {ρ⁺² : Sub ((Γ↑ ▸ A⁻) ▸ A⁺ʷ) Γ}
      {ρ⁺³ : Sub (((Γ↑ ▸ A⁻) ▸ A⁺ʷ) ▸ A↑) Γ} →
      (nΓ : NatCtx Γ (mk X X-up) Γ↑) →
      (nin⁻ : NatIn⁻ (mk X X-up) nΓ ρ⁻) →
      (nin⁺ : NatIn⁺ (mk X X-up) nΓ ρ⁺) →
      (subA⁻ : Raw.SubstTy (Raw-Ty A) (Raw-Sub ρ⁻) (Raw-Ty A⁻)) →
      (subA⁺ : Raw.SubstTy (Raw-Ty A) (Raw-Sub ρ⁺) (Raw-Ty A⁺)) →
      (wkA⁺ : Raw.WkTy {A = Raw-Ty A⁻} (Raw-Ty A⁺) (Raw-Ty A⁺ʷ)) →
      Raw.WkSub {A = Raw-Ty A⁻} (Raw-Sub ρ⁺) (Raw-Sub ρ⁺¹) →
      Raw.WkSub {A = Raw-Ty A⁺ʷ} (Raw-Sub ρ⁺¹) (Raw-Sub ρ⁺²) →
      Raw.WkSub {A = Raw-Ty A↑} (Raw-Sub ρ⁺²) (Raw-Sub ρ⁺³) →
      (px⁺ : HasTySub
        (var {Γ = (((Γ↑ ▸ A⁻) ▸ A⁺ʷ) ▸ A↑)}
          (Raw.succ Raw.zero))
        A ρ⁺³) →
      NatIn⁺
        (mk (Dep.sel-set (Raw-Ty A) X) (snoc-set X X-up))
        (natctx-set
          {A = A} {X = X} {X-up = X-up}
          {ρ⁻ = ρ⁻} {ρ⁺ = ρ⁺}
          {A⁻ = A⁻} {A⁺ = A⁺} {A⁺ʷ = A⁺ʷ} {A↑ = A↑}
          nΓ nin⁻ nin⁺ subA⁻ subA⁺ wkA⁺)
        (snocSubEq ρ⁺³ A
          (var {Γ = (((Γ↑ ▸ A⁻) ▸ A⁺ʷ) ▸ A↑)}
            (Raw.succ Raw.zero))
          px⁺)
```

## Type, term, and substitution naturality

`NatTy` is still postulated, but its surrounding context and endpoint context are
now constrained by the real relations above.

`NatTm` remains conservative: its type index is not yet forced to be the
instantiation of some `NatTy`. `NatSub` has been tightened so its target
selector is definitionally `inv-img σ X`.

```agda
postulate
  NatTy : {Γ Γ↑ Γ↑A : Ctx} →
    (X : Up Γ) →
    (nΓ : NatCtx Γ X Γ↑) →
    (A : Ty Γ) →
    NatCtxExt X nΓ A Γ↑A →
    Ty Γ↑A →
    Set₁

  NatTm : {Γ Γ↑ : Ctx} →
    (X : Up Γ) →
    NatCtx Γ X Γ↑ →
    Tm Γ →
    Ty Γ↑ →
    Tm Γ↑ →
    Set₁

  NatSub : {Δ Δ↑ Γ Γ↑ : Ctx} →
    (X : Up Δ) →
    NatCtx Δ X Δ↑ →
    (σ : Sub Δ Γ) →
    NatCtx Γ (inv-img σ X) Γ↑ →
    Sub Δ↑ Γ↑ →
    Set₁
```

## Status

Implemented as real inductive relations:

- `NatCtx`
- `NatCtxExt`
- `NatIn⁻`
- `NatIn⁺`

Still postulated:

- `NatTy`
- `NatTm`
- `NatSub`

The concrete canonical inhabitants and the remaining postulated witnesses are in
`3b-Naturality-Comp`.
