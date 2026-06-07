# 2c-BasicCoherences-Comp: Computed Basic-Coherence Helpers

The relational core `2c-BasicCoherences` packages objects, morphisms, and
the temporary coherence postulates. This companion adds the helpers that choose
computed substitution outputs.

```agda
module 2c-BasicCoherences-Comp where

import 2a-CaTT-Comp as C

open import Agda.Builtin.Equality using (_≡_)
open import 2c-BasicCoherences public

open C public
```

## Structural Helpers

```agda
postulate
  TmTyped-ext : {Γ : Ctx} {A : Ty Γ} {x y : TmTyped A}
    → Raw-Tm (TmTyped.tm x) ≡ Raw-Tm (TmTyped.tm y) → x ≡ y

  Obj-ext : {Γ : Ctx} {x y : Obj Γ}
    → Raw-Tm (Obj.tm x) ≡ Raw-Tm (Obj.tm y) → x ≡ y

  Mor-ext : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y}
    → Raw-Tm (Mor.tm f) ≡ Raw-Tm (Mor.tm g) → f ≡ g

  Mor₂-ext : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} {α β : Mor₂ f g}
    → Raw-Tm (Mor₂.tm α) ≡ Raw-Tm (Mor₂.tm β) → α ≡ β

```

## Computed Substitution Helpers

```agda
postulate
  obj-sub-typed : {Γ Δ : Ctx} → (x : Obj Δ) → (σ : Sub Γ Δ) →
    HasTy (Obj.tm x [ σ ]t) ⋆

_[_]obj : {Γ Δ : Ctx} → Obj Δ → Sub Γ Δ → Obj Γ
x [ σ ]obj = mkObj (Obj.tm x [ σ ]t) (obj-sub-typed x σ)

postulate
  mor-sub-image : {Γ Δ : Ctx} {x y : Obj Δ} → (σ : Sub Γ Δ) →
    ([⋆] x ⇒ y) [ σ ]T ≡ [⋆] (x [ σ ]obj) ⇒ (y [ σ ]obj)

  mor-sub-typed : {Γ Δ : Ctx} {x y : Obj Δ} → (f : Mor x y) → (σ : Sub Γ Δ) →
    HasTy (Mor.tm f [ σ ]t) ([⋆] (x [ σ ]obj) ⇒ (y [ σ ]obj))

_[_]mor : {Γ Δ : Ctx} {x y : Obj Δ} → Mor x y → (σ : Sub Γ Δ) →
  Mor (x [ σ ]obj) (y [ σ ]obj)
f [ σ ]mor = mkMor (Mor.tm f [ σ ]t) (mor-sub-typed f σ)

top : ∀ {Γ} {A : Ty Γ} → Sub Γ (Γ ▸ A) → Tm Γ
top {Γ} {A = A} σ = lookup (zero {Γ = Γ} {A = A}) σ
```

## Computed Coherence Images

```agda
postulate
  comp₁-sub-raw-image :
    {Γ Δ : Ctx} {x y z : Obj Δ} →
    (g : Mor y z) → (f : Mor x y) → (σ : Sub Γ Δ) →
    Raw-Tm (Mor.tm ((g •₁ f) [ σ ]mor))
      ≡
    Raw-Tm (Mor.tm ((g [ σ ]mor) •₁ (f [ σ ]mor)))
```
