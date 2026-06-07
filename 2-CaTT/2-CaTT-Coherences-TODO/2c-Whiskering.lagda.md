# 2c-Whiskering: Whiskering Coherences

```agda
module 2c-Whiskering where

import 1a-RawSyntax-Comp as Raw
import 1b-Dependency as Dep
import 1c-Pasting as Ps
import 1d-Fullness as FullMod
import 2a-CaTT-Comp as C
import 2b-Whiskering as Whisk
open import 2c-Inv public
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc; _+_; s≤s; z≤n) renaming (zero to zeroℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)

infixr 35 _∗ᵣ_
infixr 35 _∗ₗ_
```
## Right Whiskering

```agda
rwhisk-xps : Ps.VarPs (Raw-Ctx Γ-2mor) Γ-2mor-ps
rwhisk-xps = Ps.varps-weak (Ps.varps-f Ps.varps-ob) (Ps.varps-y Ps.varps-ob) (s≤s z≤n)

Γ-2mor-ob : Ctx
Γ-2mor-ob = Γ-2mor ▸ ⋆

y-2mor-ob : Obj Γ-2mor-ob
y-2mor-ob = y-2mor [ wk ]obj

z-2mor-ob : Obj Γ-2mor-ob
z-2mor-ob = mkObj (var (zero {Γ = Γ-2mor} {A = ⋆})) refl

ty-g-rwhisk : Ty Γ-2mor-ob
ty-g-rwhisk = [⋆] y-2mor-ob ⇒ z-2mor-ob

Γ-rwhisk : Ctx
Γ-rwhisk = Γ-2mor-ob ▸ ty-g-rwhisk

Γ-rwhisk-ps : Ps.CtxPs (Raw-Ctx Γ-rwhisk)
Γ-rwhisk-ps = Ps.ps-ext rwhisk-xps

x-rwhisk : Obj Γ-rwhisk
x-rwhisk = x-2mor [ wk ]obj [ wk ]obj

y-rwhisk : Obj Γ-rwhisk
y-rwhisk = y-2mor [ wk ]obj [ wk ]obj

z-rwhisk : Obj Γ-rwhisk
z-rwhisk = z-2mor-ob [ wk ]obj

f₁-rwhisk : Mor x-rwhisk y-rwhisk
f₁-rwhisk = f₁-2mor [ wk ]mor [ wk ]mor

f₂-rwhisk : Mor x-rwhisk y-rwhisk
f₂-rwhisk = f₂-2mor [ wk ]mor [ wk ]mor

α-rwhisk : Mor₂ f₁-rwhisk f₂-rwhisk
α-rwhisk = mkMor₂ ((Mor₂.tm α-2mor) [ wk ]t [ wk ]t) refl

g-rwhisk : Mor y-rwhisk z-rwhisk
g-rwhisk = mkMor (var (zero {Γ = Γ-2mor-ob} {A = ty-g-rwhisk})) refl

γ-2mor-ob : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ : Mor x y} →
  Mor₂ f₁ f₂ → (z : Obj Γ) → Sub Γ Γ-2mor-ob
γ-2mor-ob α z = ⟨ γ-2mor α , Obj.tm z ⟩:[ HasTy→tyOf≡ (Obj.hasTy z) ]

ty-g-rwhisk-image : {Γ : Ctx} {x y z : Obj Γ} {f₁ f₂ : Mor x y} →
    (α : Mor₂ f₁ f₂) → ty-g-rwhisk [ γ-2mor-ob α z ]T ≡ [⋆] y ⇒ z
ty-g-rwhisk-image α = Ty-ext refl

abstract
  γ-rwhisk-typed : {Γ : Ctx} {x y z : Obj Γ} → {f₁ f₂ : Mor x y} → (g : Mor y z) →
    (α : Mor₂ f₁ f₂) → tyOf (Mor.tm g) ≡ ty-g-rwhisk [ γ-2mor-ob α z ]T
  γ-rwhisk-typed {z = z} g α = trans
      (HasTy→tyOf≡ (Mor.hasTy g)) (sym (ty-g-rwhisk-image {z = z} α))

  γ-rwhisk-typed-raw : {Γ : Ctx} {x y z : Obj Γ} → {f₁ f₂ : Mor x y} → (g : Mor y z) →
    (α : Mor₂ f₁ f₂)
    → Raw.tyOf (Raw-Tm (Mor.tm g))
      ≡ Raw-Ty ty-g-rwhisk Raw.[ Raw-Sub (γ-2mor-ob α z) ]T
  γ-rwhisk-typed-raw {z = z} g α =
    trans (tyOf-from-tyOf (Mor.tm g)) (cong Raw-Ty (γ-rwhisk-typed {z = z} g α))

γ-rwhisk : {Γ : Ctx} {x y z : Obj Γ} → {f₁ f₂ : Mor x y} → (g : Mor y z) →
  Mor₂ f₁ f₂ → Sub Γ Γ-rwhisk
γ-rwhisk {z = z} g α = ⟨ γ-2mor-ob α z , Mor.tm g ⟩∶[ γ-rwhisk-typed-raw g α ]

abstract
  full-rwhisk :
    FullMod.Full
      (Whisk.Γ-rwhisk-ps zeroℕ (suc zeroℕ))
      (Raw-Ty (Whisk.right-whisker-tm-univ-A zeroℕ (suc zeroℕ)))
      (Raw-Tm (Whisk.right-whisker-tm-univ-u zeroℕ (suc zeroℕ)))
      (Raw-Tm (Whisk.right-whisker-tm-univ-v zeroℕ (suc zeroℕ)))
  full-rwhisk = Whisk.right-whisker-tm-univ-full-abs zeroℕ (suc zeroℕ)

rwhisk-hom-ty : {Γ : Ctx} → (x y : Obj Γ) → Ty Γ
rwhisk-hom-ty x y =
  Whisk.homTy
    ⋆
    (Obj.tm x)
    (Obj.tm y)
    (TmTyped.tp (obj-typed x))
    (TmTyped.tp (obj-typed y))

rwhisk-cell-ty : {Γ : Ctx} {x y : Obj Γ} → Mor x y → Mor x y → Ty Γ
rwhisk-cell-ty {x = x} {y = y} f₁ f₂ =
  Whisk.homTy
    (rwhisk-hom-ty x y)
    (Mor.tm f₁)
    (Mor.tm f₂)
    (mor-tp-whisk (mor-typed f₁))
    (mor-tp-whisk (mor-typed f₂))

rwhisk-cell-itgt : {Γ : Ctx} {x y : Obj Γ} → (f₁ f₂ : Mor x y) →
  Whisk.itgt (rwhisk-cell-ty f₁ f₂) (Obj.tm y)
rwhisk-cell-itgt {x = x} {y = y} f₁ f₂ =
  Whisk.itgt-step
    (mor-tp-whisk (mor-typed f₁))
    (mor-tp-whisk (mor-typed f₂))
    (Whisk.itgt-base
      (TmTyped.tp (obj-typed x))
      (TmTyped.tp (obj-typed y)))

abstract
  rwhisk-cell-typed : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ : Mor x y} →
    (α : Mor₂ f₁ f₂) → tyOf (Mor₂.tm α) ≡ rwhisk-cell-ty f₁ f₂
  rwhisk-cell-typed {f₁ = f₁} {f₂ = f₂} α =
    trans
      (HasTy→tyOf≡ (Mor₂.hasTy α))
      (Ty-ext {A = [⇒] f₁ ⇒ f₂} {A' = rwhisk-cell-ty f₁ f₂} refl)

opaque
  rwhisk-tm : {Γ : Ctx} {x y z : Obj Γ} {f₁ f₂ : Mor x y} → (g : Mor y z) →
    Mor₂ f₁ f₂ → Tm Γ
  rwhisk-tm {x = x} {y = y} {z = z} {f₁ = f₁} {f₂ = f₂} g α =
    Whisk.right-whisker-tm
      {B = ⋆}
      {A = rwhisk-cell-ty f₁ f₂}
      {y = Obj.tm y}
      {z = Obj.tm z}
      (TmTyped.tp (obj-typed y))
      (TmTyped.tp (obj-typed z))
      (TmTyped.tm (mor-typed g))
      (mor-tp-whisk (mor-typed g))
      (rwhisk-cell-itgt f₁ f₂)
      {a = Mor₂.tm α}
      (rwhisk-cell-typed α)

opaque
  unfolding rwhisk-tm _•₁_

  rwhisk-typed : {Γ : Ctx} {x y z : Obj Γ} {f₁ f₂ : Mor x y}
    (g : Mor y z) (α : Mor₂ f₁ f₂) →
    HasTy (rwhisk-tm g α) ([⇒] (g •₁ f₁) ⇒ (g •₁ f₂))
  rwhisk-typed {x = x} {y = y} {z = z} {f₁ = f₁} {f₂ = f₂} g α =
    tyOf≡→HasTy
      {t = rwhisk-tm g α}
      {A = [⇒] (g •₁ f₁) ⇒ (g •₁ f₂)}
      (trans
        (Whisk.right-whisker-tm-typed
          {B = ⋆}
          {A = rwhisk-cell-ty f₁ f₂}
          {y = Obj.tm y}
          {z = Obj.tm z}
          (TmTyped.tp (obj-typed y))
          (TmTyped.tp (obj-typed z))
          (TmTyped.tm (mor-typed g))
          (mor-tp-whisk (mor-typed g))
          (rwhisk-cell-itgt f₁ f₂)
          {a = Mor₂.tm α}
          (rwhisk-cell-typed α))
        (Ty-ext refl))

opaque
  _∗ᵣ_ : {Γ : Ctx} {x y z : Obj Γ} {f₁ f₂ : Mor x y} → (g : Mor y z) →
    Mor₂ f₁ f₂ → Mor₂ (g •₁ f₁) (g •₁ f₂)
  _∗ᵣ_ g α = mkMor₂ (rwhisk-tm g α) (rwhisk-typed g α)
```

## Left Whiskering

For the definition of left whiskering, we extend `Γ-comp` twice:
- We first add a new morphism `g₂ : y → z` parallel to `g` to get `Γ-comp-mor`,
- We then add a 2-morphism `β : g₁ → g₂` (where `g₁` stands for the existing
  `g`) to get `Γ-lwhisk`.

```agda
mor-ty-comp : Ty Γ-comp
mor-ty-comp = [⋆] y-comp ⇒ z-comp

Γ-comp-mor : Ctx
Γ-comp-mor = Γ-comp ▸ mor-ty-comp

x-comp-mor : Obj Γ-comp-mor
x-comp-mor = x-comp [ wk ]obj

y-comp-mor : Obj Γ-comp-mor
y-comp-mor = y-comp [ wk ]obj

z-comp-mor : Obj Γ-comp-mor
z-comp-mor = z-comp [ wk ]obj

f-comp-mor : Mor x-comp-mor y-comp-mor
f-comp-mor = f-comp [ wk ]mor

g₁-comp-mor : Mor y-comp-mor z-comp-mor
g₁-comp-mor = g-comp [ wk ]mor

g₂-comp-mor : Mor y-comp-mor z-comp-mor
g₂-comp-mor = mkMor (var (zero {Γ = Γ-comp} {A = mor-ty-comp})) refl

ty-β : Ty Γ-comp-mor
ty-β = [⇒] g₁-comp-mor ⇒ g₂-comp-mor

Γ-lwhisk : Ctx
Γ-lwhisk = Γ-comp-mor ▸ ty-β

Γ-lwhisk-ps : Ps.CtxPs (Raw-Ctx Γ-lwhisk)
Γ-lwhisk-ps = Ps.ps-ext (Ps.varps-f (Ps.varps-y Ps.varps-ob))

x-lwhisk : Obj Γ-lwhisk
x-lwhisk = x-comp-mor [ wk ]obj

y-lwhisk : Obj Γ-lwhisk
y-lwhisk = y-comp-mor [ wk ]obj

z-lwhisk : Obj Γ-lwhisk
z-lwhisk = z-comp-mor [ wk ]obj

f-lwhisk : Mor x-lwhisk y-lwhisk
f-lwhisk = f-comp-mor [ wk ]mor

g₁-lwhisk : Mor y-lwhisk z-lwhisk
g₁-lwhisk = g₁-comp-mor [ wk ]mor

g₂-lwhisk : Mor y-lwhisk z-lwhisk
g₂-lwhisk = g₂-comp-mor [ wk ]mor

β-lwhisk : Mor₂ g₁-lwhisk g₂-lwhisk
β-lwhisk = mkMor₂ (var (zero {Γ = Γ-comp-mor} {A = ty-β})) refl

mor-ty-comp-image : {Γ : Ctx} {x y z : Obj Γ} {g : Mor y z} (f : Mor x y) →
    mor-ty-comp [ γ-comp g f ]T ≡ [⋆] y ⇒ z
mor-ty-comp-image f = Ty-ext refl

abstract
  γ-comp-mor-typed : {Γ : Ctx} {x y z : Obj Γ} {g₁ : Mor y z}
    (f : Mor x y) (g₂ : Mor y z) →
    tyOf (Mor.tm g₂) ≡ mor-ty-comp [ γ-comp g₁ f ]T
  γ-comp-mor-typed {g₁ = g₁} f g₂ =
    trans (HasTy→tyOf≡ (Mor.hasTy g₂)) (sym (mor-ty-comp-image {g = g₁} f))

  γ-comp-mor-typed-raw : {Γ : Ctx} {x y z : Obj Γ} {g₁ : Mor y z}
    (f : Mor x y) (g₂ : Mor y z)
    → Raw.tyOf (Raw-Tm (Mor.tm g₂))
      ≡ Raw-Ty mor-ty-comp Raw.[ Raw-Sub (γ-comp g₁ f) ]T
  γ-comp-mor-typed-raw {g₁ = g₁} f g₂ =
    trans (tyOf-from-tyOf (Mor.tm g₂)) (cong Raw-Ty (γ-comp-mor-typed {g₁ = g₁} f g₂))

γ-comp-mor : {Γ : Ctx} {x y z : Obj Γ} {g₁ : Mor y z} →
  (f : Mor x y) → Mor y z → Sub Γ Γ-comp-mor
γ-comp-mor {g₁ = g₁} f g₂ =
  ⟨ γ-comp g₁ f , Mor.tm g₂ ⟩∶[ γ-comp-mor-typed-raw {g₁ = g₁} f g₂ ]

ty-β-image : {Γ : Ctx} {x y z : Obj Γ} {g₁ g₂ : Mor y z} (f : Mor x y) →
    ty-β [ γ-comp-mor {g₁ = g₁} f g₂ ]T ≡ [⇒] g₁ ⇒ g₂
ty-β-image f = Ty-ext refl

abstract
  γ-lwhisk-typed : {Γ : Ctx} {x y z : Obj Γ} {g₁ g₂ : Mor y z}
    (f : Mor x y) (β : Mor₂ g₁ g₂) →
    tyOf (Mor₂.tm β) ≡ ty-β [ γ-comp-mor {g₁ = g₁} f g₂ ]T
  γ-lwhisk-typed {g₁ = g₁} {g₂ = g₂} f β =
    trans (HasTy→tyOf≡ (Mor₂.hasTy β)) (sym (ty-β-image {g₁ = g₁} {g₂ = g₂} f))

  γ-lwhisk-typed-raw : {Γ : Ctx} {x y z : Obj Γ} {g₁ g₂ : Mor y z}
    (f : Mor x y) (β : Mor₂ g₁ g₂)
    → Raw.tyOf (Raw-Tm (Mor₂.tm β))
      ≡ Raw-Ty ty-β Raw.[ Raw-Sub (γ-comp-mor {g₁ = g₁} f g₂) ]T
  γ-lwhisk-typed-raw {g₁ = g₁} {g₂ = g₂} f β =
    trans (tyOf-from-tyOf (Mor₂.tm β)) (cong Raw-Ty (γ-lwhisk-typed {g₁ = g₁} {g₂ = g₂} f β))

γ-lwhisk : {Γ : Ctx} {x y z : Obj Γ} {g₁ g₂ : Mor y z} →
  (f : Mor x y) → Mor₂ g₁ g₂ → Sub Γ Γ-lwhisk
γ-lwhisk {g₁ = g₁} {g₂ = g₂} f β =
  ⟨ γ-comp-mor {g₁ = g₁} f g₂ , Mor₂.tm β ⟩∶[ γ-lwhisk-typed-raw {g₁ = g₁} {g₂ = g₂} f β ]

lwhisk-src-mor : Mor x-lwhisk z-lwhisk
lwhisk-src-mor = g₁-lwhisk •₁ f-lwhisk

lwhisk-tgt-mor : Mor x-lwhisk z-lwhisk
lwhisk-tgt-mor = g₂-lwhisk •₁ f-lwhisk

postulate
  full-lwhisk : FullMod.Full Γ-lwhisk-ps (Raw-Ty ([⋆] x-lwhisk ⇒ z-lwhisk))
    (Raw-Tm (Mor.tm lwhisk-src-mor))
    (Raw-Tm (Mor.tm lwhisk-tgt-mor))

lwhisk-tm : {Γ : Ctx} {x y z : Obj Γ} {g₁ g₂ : Mor y z} →
  (f : Mor x y) → Mor₂ g₁ g₂ → Tm Γ
lwhisk-tm f β = coh Γ-lwhisk-ps ([⋆] x-lwhisk ⇒ z-lwhisk)
    (Mor.tm lwhisk-src-mor) (Mor.tm lwhisk-tgt-mor)
    (Mor.hasTy lwhisk-src-mor) (Mor.hasTy lwhisk-tgt-mor)
    full-lwhisk (γ-lwhisk f β)

postulate
  lwhisk-typed : {Γ : Ctx} {x y z : Obj Γ} {g₁ g₂ : Mor y z}
    (f : Mor x y) (β : Mor₂ g₁ g₂) →
    HasTy (lwhisk-tm f β) ([⇒] (g₁ •₁ f) ⇒ (g₂ •₁ f))

opaque
  _∗ₗ_ : {Γ : Ctx} {x y z : Obj Γ} {g₁ g₂ : Mor y z} →
    (f : Mor x y) → Mor₂ g₁ g₂ → Mor₂ (g₁ •₁ f) (g₂ •₁ f)
  _∗ₗ_ f β = mkMor₂ (lwhisk-tm f β) (lwhisk-typed f β)
```
