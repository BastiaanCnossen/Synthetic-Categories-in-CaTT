# 2d-Isomorphisms: Sections, Retractions, and Isomorphisms

This module defines isomorphisms: 1-morphisms `f: x → y` that admit
both a section `s: y → x` satisfying `f •₁ s ≅ id₁ y` and a retraction
`r: y → x` satisfying `r •₁ f ≅ id₁ x`.

We further establish various closure operations:
- Composites of isomorphisms are isomorphisms
- The inverse of an isomorphism is an isomorphism
- The section of an isomorphism is also a retraction, and vice versa.

```agda
module 2d-Isomorphisms where

import 2c-BasicCoherences as Coh
open Coh public using (Ctx; Obj; Mor; Mor₂; Mor₃; [⇒]_⇒_)

infixr 30 _•₁_
infixr 30 _•₂_

id₁ : {Γ : Ctx} → (x : Obj Γ) → Mor x x
id₁ = Coh.id₁

_•₁_ : {Γ : Ctx} {x y z : Obj Γ} → Mor y z → Mor x y → Mor x z
_•₁_ = Coh._•₁_

_•₂_ : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
  Mor₂ f₂ f₃ → Mor₂ f₁ f₂ → Mor₂ f₁ f₃
_•₂_ = Coh._•₂_

_∗ᵣ_ : {Γ : Ctx} {x y z : Obj Γ} {f₁ f₂ : Mor x y} → (g : Mor y z) →
  Mor₂ f₁ f₂ → Mor₂ (g •₁ f₁) (g •₁ f₂)
_∗ᵣ_ = Coh._∗ᵣ_

_∗ₗ_ : {Γ : Ctx} {x y z : Obj Γ} {g₁ g₂ : Mor y z} →
  (f : Mor x y) → Mor₂ g₁ g₂ → Mor₂ (g₁ •₁ f) (g₂ •₁ f)
_∗ₗ_ = Coh._∗ₗ_

lunit₁ : {Γ : Ctx} {x y : Obj Γ} → (f : Mor x y) → Mor₂ (id₁ y •₁ f) f
lunit₁ = Coh.lunit₁

Inv₂ : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} → Mor₂ f g → Mor₂ g f
Inv₂ = Coh.inv₂

Inv₃ : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} {α β : Mor₂ f g} →
  Mor₃ α β → Mor₃ β α
Inv₃ = Coh.Inv₃

assoc₁ : {Γ : Ctx} {x y z w : Obj Γ}
  → (f : Mor x y) → (g : Mor y z) → (h : Mor z w)
  → Mor₂ (h •₁ (g •₁ f)) ((h •₁ g) •₁ f)
assoc₁ = Coh.assoc

assoc₁⁻¹ : {Γ : Ctx} {x y z w : Obj Γ}
  → (f : Mor x y) → (g : Mor y z) → (h : Mor z w)
  → Mor₂ ((h •₁ g) •₁ f) (h •₁ (g •₁ f))
assoc₁⁻¹ f g h = Inv₂ (assoc₁ f g h)

runit₁ : {Γ : Ctx} {x y : Obj Γ} → (f : Mor x y) → Mor₂ (f •₁ id₁ x) f
runit₁ = Coh.runit

```

## Sections and retractions

For a morphism `f : x → y`, a section of `f` is a morphism `s : y → x`
equipped with a 2-morphism witnessing `f ∘ s ⇒ id₁_y`. A retraction of `f`
is a morphism `r : y → x` together with a 2-morphism witnessing
`r ∘ f ⇒ id₁_x`.

```agda
is-Sec : {Γ : Ctx} {x y : Obj Γ} (f : Mor x y) → (g : Mor y x) → Set₁
is-Sec {y = y} f g = Mor₂ (f •₁ g) (id₁ y)

record Sec {Γ : Ctx} {x y : Obj Γ} (f : Mor x y) : Set₁ where
  constructor mkSec
  field
    map    : Mor y x
    is-sec : is-Sec f map

is-Ret : {Γ : Ctx} {x y : Obj Γ} (f : Mor x y) → (g : Mor y x) → Set₁
is-Ret {x = x} f g = Mor₂ (g •₁ f) (id₁ x)

record Ret {Γ : Ctx} {x y : Obj Γ} (f : Mor x y) : Set₁ where
  constructor mkRet
  field
    map    : Mor y x
    is-ret : is-Ret f map
```

## Isomorphisms

An isomorphism between objects `x` and `y` consists of a morphism
`f : x → y` equipped with both a section and a retraction. Since we will
eventually work in a setting where all 2-morphisms are invertible, this
biinvertible presentation is equivalent to the more symmetric notion of an
equivalence of objects.

```agda
record Inverse {Γ : Ctx} {x y : Obj Γ} (f : Mor x y) : Set₁ where
  constructor mkInverse
  field
    map : Mor y x
    inv-is-sec : is-Sec f map
    inv-is-ret : is-Ret f map 

inv-map : {Γ : Ctx} {x y : Obj Γ} {f : Mor x y} → Inverse f → Mor y x
inv-map = Inverse.map

record Iso {Γ : Ctx} (x y : Obj Γ) : Set₁ where
  constructor mkIso
  field
    map : Mor x y
    inv : Inverse map

iso-map : {Γ : Ctx} {x y : Obj Γ} → Iso x y → Mor x y
iso-map = Iso.map

iso-inv-map : {Γ : Ctx} {x y : Obj Γ} → Iso x y → Mor y x
iso-inv-map f = Inverse.map (Iso.inv f)

iso-inv-is-sec : {Γ : Ctx} {x y : Obj Γ} → (f : Iso x y)
  → is-Sec (iso-map f) (iso-inv-map f) 
iso-inv-is-sec f = Inverse.inv-is-sec (Iso.inv f)

iso-inv-is-ret : {Γ : Ctx} {x y : Obj Γ} → (f : Iso x y)
  → is-Ret (iso-map f) (iso-inv-map f) 
iso-inv-is-ret f = Inverse.inv-is-ret (Iso.inv f)
```

## Composition of isomorphisms

Isomorphisms compose: given `f : x ≅ y` and `g : y ≅ z`, we construct an
isomorphism `x ≅ z`. The forward map is `map g ∘ map f`, and the section and
retraction are obtained by composing those of `f` and `g` in the opposite
order. The witnessing 2-cells are assembled from the unit and associativity
coherences together with left and right whiskering.

```agda
iso-comp : {Γ : Ctx} {x y z : Obj Γ} → Iso y z → Iso x y → Iso x z
Iso.map (iso-comp g f) = iso-map g •₁ iso-map f
Inverse.map (Iso.inv (iso-comp g f)) = iso-inv-map f •₁ iso-inv-map g
Inverse.inv-is-sec (Iso.inv (iso-comp g f)) =
  iso-inv-is-sec g
    •₂ (iso-map g ∗ᵣ lunit₁ (iso-inv-map g))
    •₂ (iso-map g ∗ᵣ (iso-inv-map g ∗ₗ iso-inv-is-sec f))
    •₂ (iso-map g ∗ᵣ assoc₁ (iso-inv-map g) (iso-inv-map f) (iso-map f))
    •₂ assoc₁⁻¹ (iso-inv-map f •₁ iso-inv-map g) (iso-map f) (iso-map g)
Inverse.inv-is-ret (Iso.inv (iso-comp g f)) =
  iso-inv-is-ret f
    •₂ (iso-inv-map f ∗ᵣ lunit₁ (iso-map f))
    •₂ (iso-inv-map f ∗ᵣ (iso-map f ∗ₗ iso-inv-is-ret g))
    •₂ (iso-inv-map f ∗ᵣ assoc₁ (iso-map f) (iso-map g) (iso-inv-map g))
    •₂ assoc₁⁻¹ (iso-map g •₁ iso-map f) (iso-inv-map g) (iso-inv-map f)
```

## Inverse of an isomorphism

Given an isomorphism `f : x ≅ y`, its inverse map is itself an isomorphism
`y ≅ x`.  The forward map of the inverse is `iso-inv-map f`, and the
witnessing section and retraction are obtained by swapping the roles of the
original retraction and section data.

```agda
iso-inv : {Γ : Ctx} {x y : Obj Γ} → Iso x y → Iso y x
Iso.map (iso-inv f) = iso-inv-map f
Inverse.map (Iso.inv (iso-inv f)) = iso-map f
Inverse.inv-is-sec (Iso.inv (iso-inv f)) = iso-inv-is-ret f
Inverse.inv-is-ret (Iso.inv (iso-inv f)) = iso-inv-is-sec f
```

## Inverses are unique

```agda
abstract
  inv-is-unique : {Γ : Ctx} {x y : Obj Γ} {f : Mor x y}
    → (g h : Inverse f) → Mor₂ (inv-map g) (inv-map h) 
  inv-is-unique {f = f} g h =
    runit₁ (inv-map h)
      •₂ (inv-map h ∗ᵣ Inverse.inv-is-sec g)
      •₂ assoc₁⁻¹ (inv-map g) f (inv-map h)
      •₂ Inv₂ (inv-map g ∗ₗ Inverse.inv-is-ret h)
      •₂ Inv₂ (lunit₁ (inv-map g))
```

## Now the same story, one dimension higher.

```agda
data Inverse₂ {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y}
  (α : Mor₂ f g) : Set₁ where
  mkInverse₂ :
    (β : Mor₂ g f) →
    Mor₃ (Coh._•₂_ α β) (Coh.id₂ g) →
    Mor₃ (Coh._•₂_ β α) (Coh.id₂ f) →
    Inverse₂ α

inv₂-map : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y}
  {α : Mor₂ f g} → Inverse₂ α → Mor₂ g f
inv₂-map (mkInverse₂ β _ _) = β

opaque
  inv₂-is-unique : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y}
    {α : Mor₂ f g} → (p q : Inverse₂ α) → Mor₃ (inv₂-map p) (inv₂-map q)
  inv₂-is-unique {f = f} {g = g} {α = α} (mkInverse₂ βp secp _) (mkInverse₂ βq _ retq) =
    Coh._•₃_
      {α = βp}
      {β = Coh._•₂_ βq (Coh.id₂ g)}
      {γ = βq}
      (Coh.runit₂ βq)
      (Coh._•₃_
        {α = βp}
        {β = Coh._•₂_ βq (Coh._•₂_ α βp)}
        {γ = Coh._•₂_ βq (Coh.id₂ g)}
        (Coh._∗ᵣ₂_ βq secp)
        (Coh._•₃_
          {α = βp}
          {β = Coh._•₂_ (Coh._•₂_ βq α) βp}
          {γ = Coh._•₂_ βq (Coh._•₂_ α βp)}
          (Coh.assoc₂⁻¹ βp α βq)
          (Coh._•₃_
            {α = βp}
            {β = Coh._•₂_ (Coh.id₂ f) βp}
            {γ = Coh._•₂_ (Coh._•₂_ βq α) βp}
            (Coh._∗ₗ₂_ βp (Inv₃ retq))
            (Inv₃ (Coh.lunit₂ βp)))))

opaque
  2-cell-inverse : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y}
    → (α : Mor₂ f g) → Inverse₂ α
  2-cell-inverse α =
    mkInverse₂ (Inv₂ α) (Coh.inv₂-is-sec α) (Coh.inv₂-is-ret α)

opaque
  unfolding 2-cell-inverse

  inv₂-involutive : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y}
    → (α : Mor₂ f g) → Mor₃ (Inv₂ (Inv₂ α)) α
  inv₂-involutive α =
    inv₂-is-unique
      (2-cell-inverse (Inv₂ α))
      (mkInverse₂ α (Coh.inv₂-is-ret α) (Coh.inv₂-is-sec α))
```
