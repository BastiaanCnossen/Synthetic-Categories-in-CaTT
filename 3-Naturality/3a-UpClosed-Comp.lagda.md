# 3a-UpClosed-Comp: Computed Selector Compatibility

This module is the computational companion to `3a-UpClosed`. The relational core
holds the proposition-facing selector infrastructure: up-closed selectors, the
relation-native dependency transport family, and the inverse image characterized
through `SelDepSubAt`. The canonical functions `inv-img-sel` / `inv-img` and the
relation-native `-rel` lemmas live in the core.

This module re-exports that core and adds the compatibility wrappers that
genuinely need a *computed* raw operation:

- the computed-substitution factorization `no-tm-dep-sub`, stated against
  `t [ σ ]t`;
- the computed-weakening selector lemmas `var-upclose-wk-dep`,
  `var-upclose-zero-wk-no-dep`, `var-upclose-succ-wk-no-dep`, and
  `var-upclose-succ-zero-wk2-no-dep`, stated against `t [ wk ]t`.

Each wrapper instantiates the relational core lemma with the canonical computed
witness (`Raw.substTm` / `Raw.wkTm-rel`) and bridges the computed output back to
the explicit relational result. Import `3a-UpClosed` when only the relational
API is needed; import this module when a computed output is genuinely consumed.

```agda
module 3a-UpClosed-Comp where

open import 3a-UpClosed public
import 1a-RawSyntax-Comp as Raw
open import 2a-CaTT-Comp as C

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (cong; subst)
```

## Factorization Through Computed Substitution

`no-tm-dep-sub` is the computed-substitution form of the core
`sel-dep-tm-sub-factor`, supplying the canonical witness
`Raw.substTm (Raw-Tm t) (Raw-Sub σ)` for the substituted term `t [ σ ]t`.

```agda
no-tm-dep-sub :
  {Γ Δ : Ctx} →
  {σ : Sub Γ Δ} →
  {X : Up Γ} →
  {t : Tm Δ} →
  (D.SelDepTm (inv-img-sel σ X) (Raw-Tm t) → ⊥) →
  tm-dep X (t [ σ ]t) →
  ⊥
no-tm-dep-sub {σ = σ} {X = X} {t = t} no-dep dep =
  no-dep
    (sel-dep-tm-sub-factor σ X {t = t} {u = t [ σ ]t}
      (Raw.substTm (Raw-Tm t) (Raw-Sub σ)) dep)
```

## var-upclose Through Computed Weakening

These wrappers instantiate the relational core `-rel` lemmas with the canonical
weakening witness `Raw.wkTm-rel (Raw-Tm t)`, transporting the computed-weakening
hypothesis `t [ wk ]t` to the canonical raw weakening via `wkTm-sub`.

```agda
var-upclose-wk-dep :
  {Γ : Ctx} {A : Ty Γ} {x : Var Γ} →
  (t : Tm Γ) →
  tm-dep
    (var-upclose {Γ = Γ ▸ A} (succ {Γ = Γ} {A = A} x))
    (t [ wk {Γ = Γ} {A = A} ]t) →
  tm-dep (var-upclose {Γ = Γ} x) t
var-upclose-wk-dep {Γ = Γ} {A = A} {x = x} t dep =
  var-upclose-wk-dep-rel {Γ = Γ} {A = A} {x = x} t (Raw.wkTm-rel (Raw-Tm t))
    (subst
      (D.SelDepTm
        (Up.sel (var-upclose {Γ = Γ ▸ A} (succ {Γ = Γ} {A = A} x))))
      (cong Raw-Tm (wkTm-sub {A = A} t))
      dep)

var-upclose-zero-wk-no-dep :
  {Γ : Ctx} {A : Ty Γ} → (t : Tm Γ) →
  tm-dep (var-upclose (zero {Γ = Γ} {A = A})) (t [ wk {Γ = Γ} {A = A} ]t) → ⊥
var-upclose-zero-wk-no-dep {Γ = Γ} {A = A} t dep =
  var-upclose-zero-wk-no-dep-rel {Γ = Γ} {A = A} t (Raw.wkTm-rel (Raw-Tm t))
    (subst
      (D.SelDepTm (Up.sel (var-upclose {Γ = Γ ▸ A} (zero {Γ = Γ} {A = A}))))
      (cong Raw-Tm (wkTm-sub {A = A} t))
      dep)

var-upclose-succ-wk-no-dep :
  {Γ : Ctx} {A : Ty Γ} {B : Ty (Γ ▸ A)}
  {x : Var (Γ ▸ A)} → (t : Tm (Γ ▸ A)) →
  (tm-dep (var-upclose x) t → ⊥) →
  tm-dep
    (var-upclose (succ {Γ = Γ ▸ A} {A = B} x))
    (t [ wk {Γ = Γ ▸ A} {A = B} ]t) →
  ⊥
var-upclose-succ-wk-no-dep {Γ = Γ} {A = A} {B = B} {x = x} t no-dep dep =
  var-upclose-succ-wk-no-dep-rel {Γ = Γ} {A = A} {B = B} {x = x} t
    (Raw.wkTm-rel (Raw-Tm t)) no-dep
    (subst
      (D.SelDepTm
        (Up.sel (var-upclose {Γ = (Γ ▸ A) ▸ B} (succ {Γ = Γ ▸ A} {A = B} x))))
      (cong Raw-Tm (wkTm-sub {A = B} t))
      dep)

var-upclose-succ-zero-wk2-no-dep :
  {Γ : Ctx} {A : Ty Γ} {B : Ty (Γ ▸ A)} → (t : Tm Γ) →
  tm-dep
    (var-upclose (succ {Γ = Γ ▸ A} {A = B} (zero {Γ = Γ} {A = A})))
    ((t [ wk {Γ = Γ} {A = A} ]t) [ wk {Γ = Γ ▸ A} {A = B} ]t) →
  ⊥
var-upclose-succ-zero-wk2-no-dep {Γ = Γ} {A = A} {B = B} t dep =
  var-upclose-succ-wk-no-dep
    {Γ = Γ} {A = A} {B = B}
    {x = zero {Γ = Γ} {A = A}}
    (t [ wk {Γ = Γ} {A = A} ]t)
    (var-upclose-zero-wk-no-dep {Γ = Γ} {A = A} t)
    dep
```
