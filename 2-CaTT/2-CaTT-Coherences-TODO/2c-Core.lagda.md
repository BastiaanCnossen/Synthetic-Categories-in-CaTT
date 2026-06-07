# 2c-Core: Core Types and Substitutions

This file packages the basic categorical coherence operations directly in the
syntax of `2a-CaTT`.

We keep the archive-style explicit contexts and substitutions because they make
later instantiations much faster for Agda. The actual composition and right
whiskering terms are taken from the current `2b-Whiskering`
implementation. The identity, unit, and associativity coherences are assembled
here from those ingredients.

```agda
module 2c-Core where

import 1a-RawSyntax as Raw
import 1b-Dependency as Dep
import 1c-Pasting as Ps
import 1z-Uniqueness as Uniq
import 1d-Fullness as FullMod
import 2a-CaTT-Comp as C
import 2b-Whiskering as Whisk

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc; _+_; s≤s; z≤n) renaming (zero to zeroℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)

open C public

infixr 20 [⋆]_⇒_
infixr 20 [⇒]_⇒_
```

## Objects, Morphisms, and 2-Morphisms

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

record Mor₃ {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} (α β : Mor₂ f g) : Set₁ where
  constructor mkMor₃
  field
    tm : Tm Γ
    hasTy : HasTy tm (homTy ([⇒] f ⇒ g) (Mor₂.tm α) (Mor₂.tm β) (Mor₂.hasTy α) (Mor₂.hasTy β))

open Mor₃ public
```

### Extensional ty for Obj, Mor, Mor₂

```agda
opaque
  TmTyped-ext : {Γ : Ctx} {A : Ty Γ} {x y : TmTyped A}
    → Raw-Tm (TmTyped.tm x) ≡ Raw-Tm (TmTyped.tm y) → x ≡ y
  TmTyped-ext {x = mk (mkTm r rwf) p} {y = mk (mkTm .r rwf') q} refl
    with Tm-iswf-uip r rwf rwf'
  ... | refl = cong (mk (mkTm r rwf)) (Uniq.HasTy-uip p q)

  Obj-ext : {Γ : Ctx} {x y : Obj Γ}
    → Raw-Tm (Obj.tm x) ≡ Raw-Tm (Obj.tm y) → x ≡ y
  Obj-ext {x = mkObj (mkTm r rwf) p} {y = mkObj (mkTm .r rwf') q} refl
    with Tm-iswf-uip r rwf rwf'
  ... | refl = cong (mkObj (mkTm r rwf)) (Uniq.HasTy-uip p q)

  Mor-ext : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y}
    → Raw-Tm (Mor.tm f) ≡ Raw-Tm (Mor.tm g) → f ≡ g
  Mor-ext {f = mkMor (mkTm r rwf) p} {g = mkMor (mkTm .r rwf') q} refl
    with Tm-iswf-uip r rwf rwf'
  ... | refl = cong (mkMor (mkTm r rwf)) (Uniq.HasTy-uip p q)

  Mor₂-ext : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} {α β : Mor₂ f g}
    → Raw-Tm (Mor₂.tm α) ≡ Raw-Tm (Mor₂.tm β) → α ≡ β
  Mor₂-ext {α = mkMor₂ (mkTm r rwf) p} {β = mkMor₂ (mkTm .r rwf') q} refl
    with Tm-iswf-uip r rwf rwf'
  ... | refl = cong (mkMor₂ (mkTm r rwf)) (Uniq.HasTy-uip p q)
```

### Substitutions of objects and morphisms

```agda

opaque
  obj-sub-typed : {Γ Δ : Ctx} → (x : Obj Δ) → (σ : Sub Γ Δ) → HasTy (Obj.tm x [ σ ]t) ⋆
  obj-sub-typed {Γ = Γ} {Δ = Δ} x σ =
    tmSub-typed {Γ = Γ} {Δ = Δ} {t = Obj.tm x} {A = ⋆} {σ = σ} (Obj.hasTy x)

_[_]obj : {Γ Δ : Ctx} → Obj Δ → Sub Γ Δ → Obj Γ
x [ σ ]obj = mkObj (Obj.tm x [ σ ]t) (obj-sub-typed x σ)

abstract
  mor-sub-image : {Γ Δ : Ctx} {x y : Obj Δ} → (σ : Sub Γ Δ) →
    ([⋆] x ⇒ y) [ σ ]T ≡ [⋆] (x [ σ ]obj) ⇒ (y [ σ ]obj)
  mor-sub-image {x = x} {y = y} σ = Ty-ext {A = ([⋆] x ⇒ y) [ σ ]T}
      {A' = [⋆] (x [ σ ]obj) ⇒ (y [ σ ]obj)} refl

  mor-sub-typed : {Γ Δ : Ctx} {x y : Obj Δ} → (f : Mor x y) → (σ : Sub Γ Δ) →
    HasTy (Mor.tm f [ σ ]t) ([⋆] (x [ σ ]obj) ⇒ (y [ σ ]obj))
  mor-sub-typed {Γ = Γ} {Δ = Δ} {x = x} {y = y} f σ =
    subst (HasTy (Mor.tm f [ σ ]t))
      (mor-sub-image {x = x} {y = y} σ)
      (tmSub-typed {Γ = Γ} {Δ = Δ} {t = Mor.tm f} {A = [⋆] x ⇒ y} {σ = σ} (Mor.hasTy f))

_[_]mor : {Γ Δ : Ctx} {x y : Obj Δ} → Mor x y → (σ : Sub Γ Δ) → 
  Mor (x [ σ ]obj) (y [ σ ]obj)
f [ σ ]mor = mkMor (Mor.tm f [ σ ]t) (mor-sub-typed f σ)

top : ∀ {Γ} {A : Ty Γ} → Sub Γ (Γ ▸ A) → Tm Γ
top {Γ} {A = A} σ = lookup (zero {Γ = Γ} {A = A}) σ
```


## Typed Converters

```agda
obj-typed : {Γ : Ctx} → Obj Γ → TmTyped ⋆
obj-typed x = mk (Obj.tm x) (Obj.hasTy x)

-- MorTy (obj-typed x) (obj-typed y) reduces definitionally to [⋆] x ⇒ y,
-- so the typing witness transports without any conversion.
typed-mor : {Γ : Ctx} {x y : Obj Γ} →
  MorTm (obj-typed x) (obj-typed y) → Mor x y
typed-mor (mk tm tp) = mkMor tm tp

typed-obj : {Γ : Ctx} → TmTyped {Γ} ⋆ → Obj Γ
typed-obj (mk tm tp) = mkObj tm tp

typed-mor₁ : {Γ : Ctx} {x y : TmTyped {Γ} ⋆} →
  MorTm x y → Mor (typed-obj x) (typed-obj y)
typed-mor₁ (mk tm tp) = mkMor tm tp

-- Legacy equality interface for the (to-be-redesigned) whiskering layer.
-- The witness TmTyped.tp f is already a HasTy proof; the consumers still
-- expect a tyOf-equality, so we read it off here.  Remove once whiskering
-- is rebuilt on HasTy.
mor-tp-whisk : {Γ : Ctx} {A : Ty Γ} {x y : TmTyped A} →
  (f : MorTm x y) →
  tyOf (TmTyped.tm f) ≡ Whisk.homTy A (TmTyped.tm x) (TmTyped.tm y) (TmTyped.tp x) (TmTyped.tp y)
mor-tp-whisk {A = A} {x = x} {y = y} f =
  trans (HasTy→tyOf≡ (TmTyped.tp f))
    (Ty-ext {A = MorTy x y}
            {A' = Whisk.homTy A (TmTyped.tm x) (TmTyped.tm y) (TmTyped.tp x) (TmTyped.tp y)}
            refl)

mor-typed : {Γ : Ctx} {x y : Obj Γ} → Mor x y → MorTm (obj-typed x) (obj-typed y)
mor-typed f = mk (Mor.tm f) (Mor.hasTy f)

mor2-typed : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
  Mor₂ f g → MorTm (mor-typed f) (mor-typed g)
mor2-typed α = mk (Mor₂.tm α) (Mor₂.hasTy α)

typed-mor2 : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
  MorTm (mor-typed f) (mor-typed g) → Mor₂ f g
typed-mor2 (mk tm tp) = mkMor₂ tm tp

mor3-typed : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} {α β : Mor₂ f g} →
  Mor₃ α β → MorTm (mor2-typed α) (mor2-typed β)
mor3-typed θ = mk (Mor₃.tm θ) (Mor₃.hasTy θ)

typed-mor3 : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} {α β : Mor₂ f g} →
  MorTm (mor2-typed α) (mor2-typed β) → Mor₃ α β
typed-mor3 (mk tm tp) = mkMor₃ tm tp
```
