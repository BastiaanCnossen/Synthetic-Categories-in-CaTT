# 2c-BasicCoherences: Postulated Basic Coherences

This file is a stub. It records the object/morphism wrappers and their basic
projection behavior, but postulates the coherence operations used downstream.

Several of the coherence operations were written out before: see the folder
Agda formalization\I-CaTT\2-CaTT\2-CaTT-Coherences-TODO for various older
files. The contents of these files are somewhat outdated.

```agda
module 2c-BasicCoherences where

import 2a-CaTT as C

open import Agda.Builtin.Equality using (_≡_)

open C public

infixr 20 [⋆]_⇒_
infixr 20 [⇒]_⇒_
infixr 20 [⇒₂]_⇒_
infixr 30 _•_
infixr 30 _•₁_
infixr 30 _•₂_
infixr 30 _•₃_
infixr 35 _∗ᵣ_
infixr 35 _∗ₗ_
```

## Objects, Morphisms, And 2-Morphisms

```agda
record Obj (Γ : Ctx) : Set₁ where
  constructor mkObj
  field
    tm : Tm Γ
    hasTy : HasTy tm ⋆

open Obj public

[⋆]_⇒_ : {Γ : Ctx} → Obj Γ → Obj Γ → Ty Γ
[⋆] x ⇒ y = homTy ⋆ (Obj.tm x) (Obj.tm y) (Obj.hasTy x) (Obj.hasTy y)

record Mor {Γ : Ctx} (x y : Obj Γ) : Set₁ where
  constructor mkMor
  field
    tm : Tm Γ
    hasTy : HasTy tm ([⋆] x ⇒ y)

open Mor public

[⇒]_⇒_ : {Γ : Ctx} {x y : Obj Γ} → Mor x y → Mor x y → Ty Γ
[⇒]_⇒_ {x = x} {y = y} f g =
  homTy ([⋆] x ⇒ y) (Mor.tm f) (Mor.tm g) (Mor.hasTy f) (Mor.hasTy g)

record Mor₂ {Γ : Ctx} {x y : Obj Γ} (f g : Mor x y) : Set₁ where
  constructor mkMor₂
  field
    tm : Tm Γ
    hasTy : HasTy tm ([⇒] f ⇒ g)

open Mor₂ public

[⇒₂]_⇒_ : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} → Mor₂ f g → Mor₂ f g → Ty Γ
[⇒₂]_⇒_ {f = f} {g = g} α β =
  homTy ([⇒] f ⇒ g) (Mor₂.tm α) (Mor₂.tm β) (Mor₂.hasTy α) (Mor₂.hasTy β)

record Mor₃ {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} (α β : Mor₂ f g) : Set₁ where
  constructor mkMor₃
  field
    tm : Tm Γ
    hasTy : HasTy tm ([⇒₂] α ⇒ β)

open Mor₃ public
```

## Typed-Term Bridges

```agda
obj-typed : {Γ : Ctx} → Obj Γ → TmTyped ⋆
obj-typed x = mk (Obj.tm x) (Obj.hasTy x)

typed-obj : {Γ : Ctx} → TmTyped {Γ} ⋆ → Obj Γ
typed-obj (mk tm tp) = mkObj tm tp

postulate
  typed-mor : {Γ : Ctx} {x y : Obj Γ} →
    MorTm (obj-typed x) (obj-typed y) → Mor x y

  typed-mor₁ : {Γ : Ctx} {x y : TmTyped {Γ} ⋆} →
    MorTm x y → Mor (typed-obj x) (typed-obj y)

  mor-typed : {Γ : Ctx} {x y : Obj Γ} →
    Mor x y → MorTm (obj-typed x) (obj-typed y)

  mor2-typed : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    Mor₂ f g → MorTm (mor-typed f) (mor-typed g)

  typed-mor2 : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    MorTm (mor-typed f) (mor-typed g) → Mor₂ f g
```

## Basic Coherence Operations

```agda
postulate
  id : {Γ : Ctx} → (x : Obj Γ) → Mor x x

id₁ : {Γ : Ctx} → (x : Obj Γ) → Mor x x
id₁ = id

postulate
  _•₁_ : {Γ : Ctx} {x y z : Obj Γ} → Mor y z → Mor x y → Mor x z

_•_ : {Γ : Ctx} {x y z : Obj Γ} → Mor y z → Mor x y → Mor x z
_•_ = _•₁_

comp : {Γ : Ctx} {x y z : Obj Γ} → Mor y z → Mor x y → Mor x z
comp = _•₁_

postulate
  comp₁-raw-cong :
    {Γ : Ctx} {x y z x' y' z' : Obj Γ} →
    (g : Mor y z) → (f : Mor x y) →
    (g' : Mor y' z') → (f' : Mor x' y') →
    Raw-Tm (Obj.tm x) ≡ Raw-Tm (Obj.tm x') →
    Raw-Tm (Obj.tm y) ≡ Raw-Tm (Obj.tm y') →
    Raw-Tm (Obj.tm z) ≡ Raw-Tm (Obj.tm z') →
    Raw-Tm (Mor.tm g) ≡ Raw-Tm (Mor.tm g') →
    Raw-Tm (Mor.tm f) ≡ Raw-Tm (Mor.tm f') →
    Raw-Tm (Mor.tm (g •₁ f))
      ≡
    Raw-Tm (Mor.tm (g' •₁ f'))

  _•₂_ : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
    Mor₂ f₂ f₃ → Mor₂ f₁ f₂ → Mor₂ f₁ f₃

  lunit : {Γ : Ctx} {x y : Obj Γ} → (f : Mor x y) → Mor₂ (id y •₁ f) f

lunit₁ : {Γ : Ctx} {x y : Obj Γ} → (f : Mor x y) → Mor₂ (id₁ y •₁ f) f
lunit₁ = lunit

postulate
  runit : {Γ : Ctx} {x y : Obj Γ} → (f : Mor x y) → Mor₂ (f •₁ id x) f

  assoc : {Γ : Ctx} {x y z w : Obj Γ} →
    (f : Mor x y) → (g : Mor y z) → (h : Mor z w) →
    Mor₂ (h •₁ (g •₁ f)) ((h •₁ g) •₁ f)

  assoc⁻¹ : {Γ : Ctx} {x y z w : Obj Γ} →
    (f : Mor x y) → (g : Mor y z) → (h : Mor z w) →
    Mor₂ ((h •₁ g) •₁ f) (h •₁ (g •₁ f))

  _∗ᵣ_ : {Γ : Ctx} {x y z : Obj Γ} {f₁ f₂ : Mor x y} →
    (g : Mor y z) → Mor₂ f₁ f₂ → Mor₂ (g •₁ f₁) (g •₁ f₂)

  _∗ₗ_ : {Γ : Ctx} {x y z : Obj Γ} {g₁ g₂ : Mor y z} →
    (f : Mor x y) → Mor₂ g₁ g₂ → Mor₂ (g₁ •₁ f) (g₂ •₁ f)
```

## Higher Coherence Operations

```agda
postulate
  id₂ : {Γ : Ctx} {x y : Obj Γ} → (f : Mor x y) → Mor₂ f f

  inv₂ : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} → Mor₂ f g → Mor₂ g f

  _•₃_ : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} {α β γ : Mor₂ f g} →
    Mor₃ β γ → Mor₃ α β → Mor₃ α γ

  Inv₃ : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} {α β : Mor₂ f g} →
    Mor₃ α β → Mor₃ β α

  lunit₂ : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) → Mor₃ (id₂ g •₂ α) α

  runit₂ : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) → Mor₃ (α •₂ id₂ f) α

  assoc₂⁻¹ : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ f₄ : Mor x y} →
    (α : Mor₂ f₁ f₂) → (β : Mor₂ f₂ f₃) → (γ : Mor₂ f₃ f₄) →
    Mor₃ ((γ •₂ β) •₂ α) (γ •₂ (β •₂ α))

  _∗ᵣ₂_ : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
    (γ : Mor₂ f₂ f₃) → {α β : Mor₂ f₁ f₂} →
    Mor₃ α β → Mor₃ (γ •₂ α) (γ •₂ β)

  _∗ₗ₂_ : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
    (α : Mor₂ f₁ f₂) → {β γ : Mor₂ f₂ f₃} →
    Mor₃ β γ → Mor₃ (β •₂ α) (γ •₂ α)

  inv₂-is-sec : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) → Mor₃ (α •₂ inv₂ α) (id₂ g)

  inv₂-is-ret : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) → Mor₃ (inv₂ α •₂ α) (id₂ f)

  inv₂-involutive-whisker-square :
    {Γ : Ctx} {t x y z : Obj Γ} →
    (f : Mor x z) → (g : Mor y z) →
    (h : Mor t x) → (k : Mor t y) →
    (α : Mor₂ (f •₁ h) (g •₁ k)) →
    Mor₃
      ((g ∗ᵣ id₂ k) •₂ α)
      ((inv₂ (inv₂ α)) •₂ (f ∗ᵣ id₂ h))

  inv₂-involutive-naturality-square :
    {Γ : Ctx} {x y : Obj Γ} {src tgt : Mor x y} →
    (src-id : Mor₂ src src) →
    (tgt-id : Mor₂ tgt tgt) →
    (α : Mor₂ src tgt) →
    Mor₃
      (tgt-id •₂ α)
      ((inv₂ (inv₂ α)) •₂ src-id)
```
