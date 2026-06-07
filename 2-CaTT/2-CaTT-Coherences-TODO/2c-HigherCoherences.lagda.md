# 2c-HigherCoherences: One-Dimension-Higher Wrappers

```agda
module 2c-HigherCoherences where

import 1b-Dependency as Dep
import 1c-Pasting as Ps
import 1d-Fullness as FullMod
import 2b-Whiskering as Whisk
import 1a-RawSyntax-Comp as Raw
open import 2c-Whiskering public
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

infixr 35 _∗ᵣ₂_
infixr 35 _∗ₗ₂_
```

## Units And Associativity One Dimension Up

```agda
opaque
  lunit₂-ty : Ty Γ-2mor
  lunit₂-ty = MorTy f₁-2morᵀ f₂-2morᵀ

opaque
  unfolding f₁-2morᵀ f₂-2morᵀ

  lunit₂-srcᵀ : MorTm f₁-2morᵀ f₂-2morᵀ
  lunit₂-srcᵀ = mor2-typed (id₂ f₂-2mor •₂ α-2mor)

opaque
  unfolding f₁-2morᵀ f₂-2morᵀ

  lunit₂-tgtᵀ : MorTm f₁-2morᵀ f₂-2morᵀ
  lunit₂-tgtᵀ = mor2-typed α-2mor

opaque
  unfolding lunit₂-ty

  lunit₂-src-typed : HasTy (TmTyped.tm lunit₂-srcᵀ) lunit₂-ty
  lunit₂-src-typed = tyOf≡→HasTy (TmTyped.tp lunit₂-srcᵀ)

opaque
  unfolding lunit₂-ty

  lunit₂-tgt-typed : HasTy (TmTyped.tm lunit₂-tgtᵀ) lunit₂-ty
  lunit₂-tgt-typed = tyOf≡→HasTy (TmTyped.tp lunit₂-tgtᵀ)

opaque
  unfolding f₁-2morᵀ f₂-2morᵀ lunit₂-ty lunit₂-srcᵀ lunit₂-tgtᵀ

  lunit₂-full :
    FullMod.Full Γ-2mor-ps
      (Raw-Ty lunit₂-ty)
      (Raw-Tm (TmTyped.tm lunit₂-srcᵀ))
      (Raw-Tm (TmTyped.tm lunit₂-tgtᵀ))
  lunit₂-full =
    FullMod.full-COMPCOH
      (λ z →
        comp₂-dep-left
          {α₂ = id₂ f₂-2mor}
          {α₁ = α-2mor}
          z
          (α-2mor-dep-all z)
        , α-2mor-dep-all z)

opaque
  lunit₂-disk-tm : Tm Γ-2mor
  lunit₂-disk-tm =
    coh Γ-2mor-ps lunit₂-ty
      (TmTyped.tm lunit₂-srcᵀ)
      (TmTyped.tm lunit₂-tgtᵀ)
      lunit₂-src-typed
      lunit₂-tgt-typed
      lunit₂-full
      (idS Γ-2mor)

opaque
  lunit₂-tm : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) → Tm Γ
  lunit₂-tm α = lunit₂-disk-tm [ γ-2mor α ]t

opaque
  unfolding lunit₂-tm lunit₂-disk-tm lunit₂-ty lunit₂-srcᵀ lunit₂-tgtᵀ _•₂_ comp₂-direct id₂ id₂-direct

  lunit₂-typed : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) →
    HasTy (lunit₂-tm α)
      (homTy ([⇒] f ⇒ g)
        (Mor₂.tm (id₂ g •₂ α))
        (Mor₂.tm α)
        (Mor₂.hasTy (id₂ g •₂ α))
        (Mor₂.hasTy α))
  lunit₂-typed α = refl

opaque
  lunit₂ : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) → Mor₃ (id₂ g •₂ α) α
  lunit₂ α = mkMor₃ (lunit₂-tm α) (lunit₂-typed α)

opaque
  runit₂-ty : Ty Γ-2mor
  runit₂-ty = MorTy f₁-2morᵀ f₂-2morᵀ

opaque
  unfolding f₁-2morᵀ f₂-2morᵀ

  runit₂-srcᵀ : MorTm f₁-2morᵀ f₂-2morᵀ
  runit₂-srcᵀ = mor2-typed (α-2mor •₂ id₂ f₁-2mor)

opaque
  unfolding f₁-2morᵀ f₂-2morᵀ

  runit₂-tgtᵀ : MorTm f₁-2morᵀ f₂-2morᵀ
  runit₂-tgtᵀ = mor2-typed α-2mor

opaque
  unfolding runit₂-ty

  runit₂-src-typed : HasTy (TmTyped.tm runit₂-srcᵀ) runit₂-ty
  runit₂-src-typed = tyOf≡→HasTy (TmTyped.tp runit₂-srcᵀ)

opaque
  unfolding runit₂-ty

  runit₂-tgt-typed : HasTy (TmTyped.tm runit₂-tgtᵀ) runit₂-ty
  runit₂-tgt-typed = tyOf≡→HasTy (TmTyped.tp runit₂-tgtᵀ)

opaque
  unfolding f₁-2morᵀ f₂-2morᵀ runit₂-ty runit₂-srcᵀ runit₂-tgtᵀ

  runit₂-full :
    FullMod.Full Γ-2mor-ps
      (Raw-Ty runit₂-ty)
      (Raw-Tm (TmTyped.tm runit₂-srcᵀ))
      (Raw-Tm (TmTyped.tm runit₂-tgtᵀ))
  runit₂-full =
    FullMod.full-COMPCOH
      (λ z →
        comp₂-dep-right
          {α₂ = α-2mor}
          {α₁ = id₂ f₁-2mor}
          z
          (α-2mor-dep-all z)
        , α-2mor-dep-all z)

opaque
  runit₂-disk-tm : Tm Γ-2mor
  runit₂-disk-tm =
    coh Γ-2mor-ps runit₂-ty
      (TmTyped.tm runit₂-srcᵀ)
      (TmTyped.tm runit₂-tgtᵀ)
      runit₂-src-typed
      runit₂-tgt-typed
      runit₂-full
      (idS Γ-2mor)

opaque
  runit₂-tm : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) → Tm Γ
  runit₂-tm α = runit₂-disk-tm [ γ-2mor α ]t

opaque
  unfolding runit₂-tm runit₂-disk-tm runit₂-ty runit₂-srcᵀ runit₂-tgtᵀ _•₂_ comp₂-direct id₂ id₂-direct

  runit₂-typed : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) →
    HasTy (runit₂-tm α)
      (homTy ([⇒] f ⇒ g)
        (Mor₂.tm (α •₂ id₂ f))
        (Mor₂.tm α)
        (Mor₂.hasTy (α •₂ id₂ f))
        (Mor₂.hasTy α))
  runit₂-typed α = refl

opaque
  runit₂ : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) → Mor₃ (α •₂ id₂ f) α
  runit₂ α = mkMor₃ (runit₂-tm α) (runit₂-typed α)

f₃-2comp-ps : VarPs Γ-2comp Γ-2comp-ps
f₃-2comp-ps = Ps.varps-y f₂-2mor-ps

f₄-2assoc-ty : Ty Γ-2comp
f₄-2assoc-ty = varps-to-type f₃-2comp-ps

Γ-2assoc-mor : Ctx
Γ-2assoc-mor = Γ-2comp ▸ f₄-2assoc-ty

γ-2assoc-ty : Ty Γ-2assoc-mor
γ-2assoc-ty =
  [ wkTy f₄-2assoc-ty ]
    vs (Ps.varps-to-var f₃-2comp-ps) ⇒ vz :[ refl , refl ]

Γ-2assoc : Ctx
Γ-2assoc = Γ-2assoc-mor ▸ γ-2assoc-ty

Γ-2assoc-ps : CtxPs Γ-2assoc
Γ-2assoc-ps = Ps.ps-ext f₃-2comp-ps

wk-2assoc-mor : Sub Γ-2assoc-mor Γ-2comp
wk-2assoc-mor = wk {Γ = Γ-2comp} {A = f₄-2assoc-ty}

wk-2assoc : Sub Γ-2assoc Γ-2assoc-mor
wk-2assoc = wk {Γ = Γ-2assoc-mor} {A = γ-2assoc-ty}

x-2assoc : Obj Γ-2assoc
x-2assoc = x-2comp [ wk-2assoc-mor ]obj [ wk-2assoc ]obj

y-2assoc : Obj Γ-2assoc
y-2assoc = y-2comp [ wk-2assoc-mor ]obj [ wk-2assoc ]obj

f₁-2assoc : Mor x-2assoc y-2assoc
f₁-2assoc = f₁-2comp [ wk-2assoc-mor ]mor [ wk-2assoc ]mor

f₂-2assoc : Mor x-2assoc y-2assoc
f₂-2assoc = f₂-2comp [ wk-2assoc-mor ]mor [ wk-2assoc ]mor

f₃-2assoc : Mor x-2assoc y-2assoc
f₃-2assoc = f₃-2comp [ wk-2assoc-mor ]mor [ wk-2assoc ]mor

f₄-2assoc : Mor x-2assoc y-2assoc
f₄-2assoc =
  mkMor
    (var (succ {Γ = Γ-2assoc-mor} {A = γ-2assoc-ty}
      (zero {Γ = Γ-2comp} {A = f₄-2assoc-ty})))
    refl

α-2assoc : Mor₂ f₁-2assoc f₂-2assoc
α-2assoc =
  mkMor₂ (Mor₂.tm α₁-2comp [ wk-2assoc-mor ]t [ wk-2assoc ]t) refl

β-2assoc : Mor₂ f₂-2assoc f₃-2assoc
β-2assoc =
  mkMor₂ (Mor₂.tm α₂-2comp [ wk-2assoc-mor ]t [ wk-2assoc ]t) refl

γ-2assoc-cell : Mor₂ f₃-2assoc f₄-2assoc
γ-2assoc-cell =
  mkMor₂ (var (zero {Γ = Γ-2assoc-mor} {A = γ-2assoc-ty})) refl

assoc₂-mor-ty-image :
  {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ f₄ : Mor x y}
  → (β : Mor₂ f₂ f₃) → (α : Mor₂ f₁ f₂)
  → f₄-2assoc-ty [ γ-2comp β α ]T ≡ [⋆] x ⇒ y
assoc₂-mor-ty-image {x = x} {y = y} β α =
  Ty-ext
    {A = f₄-2assoc-ty [ γ-2comp β α ]T}
    {A' = [⋆] x ⇒ y}
    refl

γ-2assoc-mor-typed :
  {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ f₄ : Mor x y}
  → (β : Mor₂ f₂ f₃) → (α : Mor₂ f₁ f₂)
  → tyOf (Mor.tm f₄) ≡ f₄-2assoc-ty [ γ-2comp β α ]T
γ-2assoc-mor-typed {x = x} {y = y} {f₄ = f₄} β α =
  trans
    {i = tyOf (Mor.tm f₄)}
    {j = [⋆] x ⇒ y}
    {k = f₄-2assoc-ty [ γ-2comp β α ]T}
    (HasTy→tyOf≡ (Mor.hasTy f₄))
    (sym (assoc₂-mor-ty-image {x = x} {y = y} {f₄ = f₄} β α))

γ-2assoc-mor :
  {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ f₄ : Mor x y}
  → (β : Mor₂ f₂ f₃) → (α : Mor₂ f₁ f₂)
  → Sub Γ Γ-2assoc-mor
γ-2assoc-mor {f₄ = f₄} β α =
  ⟨_,_⟩:[_]
    (γ-2comp β α)
    {A = f₄-2assoc-ty}
    (Mor.tm f₄)
    (γ-2assoc-mor-typed {f₄ = f₄} β α)

assoc₂-cell-ty-image :
  {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ f₄ : Mor x y}
  → (γ : Mor₂ f₃ f₄) → (β : Mor₂ f₂ f₃) → (α : Mor₂ f₁ f₂)
  → γ-2assoc-ty [ γ-2assoc-mor {f₄ = f₄} β α ]T ≡ [⇒] f₃ ⇒ f₄
assoc₂-cell-ty-image {f₃ = f₃} {f₄ = f₄} γ β α =
  Ty-ext
    {A = γ-2assoc-ty [ γ-2assoc-mor {f₄ = f₄} β α ]T}
    {A' = [⇒] f₃ ⇒ f₄}
    refl

abstract
  γ-2assoc-typed-raw :
    {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ f₄ : Mor x y}
    → (γ : Mor₂ f₃ f₄) → (β : Mor₂ f₂ f₃) → (α : Mor₂ f₁ f₂)
    → Raw.tyOf (Raw-Tm (Mor₂.tm γ))
      ≡
      Raw-Ty γ-2assoc-ty
        Raw.[ Raw-Sub (γ-2assoc-mor {f₄ = f₄} β α) ]T
  γ-2assoc-typed-raw γ β α =
    trans
      (Mor₂.hasTy γ)
      (cong Raw-Ty (sym (assoc₂-cell-ty-image γ β α)))

γ-2assoc :
  {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ f₄ : Mor x y}
  → Mor₂ f₃ f₄ → Mor₂ f₂ f₃ → Mor₂ f₁ f₂
  → Sub Γ Γ-2assoc
γ-2assoc {f₄ = f₄} γ β α =
  ⟨ γ-2assoc-mor {f₄ = f₄} β α , Mor₂.tm γ ⟩∶[
    γ-2assoc-typed-raw γ β α ]

assoc₂-ty : Ty Γ-2assoc
assoc₂-ty = [⇒] f₁-2assoc ⇒ f₄-2assoc

assoc₂-src : Mor₂ f₁-2assoc f₄-2assoc
assoc₂-src = γ-2assoc-cell •₂ (β-2assoc •₂ α-2assoc)

assoc₂-tgt : Mor₂ f₁-2assoc f₄-2assoc
assoc₂-tgt = (γ-2assoc-cell •₂ β-2assoc) •₂ α-2assoc

abstract
  α-2assoc-dep-tail :
    (z : Var Γ-2mor) →
    Dep.DepVarTm
      (Raw.succ (Raw.succ (Raw.succ (Raw.succ z))))
      (Raw-Tm (Mor₂.tm α-2assoc))
  α-2assoc-dep-tail z =
    Whisk.dep-tm-wk
      (Whisk.dep-tm-wk
        (Whisk.dep-tm-wk
          (Whisk.dep-tm-wk (α-2mor-dep-all z))))

  β-2assoc-dep-self :
    Dep.DepVarTm
      (Raw.succ (Raw.succ Raw.zero))
      (Raw-Tm (Mor₂.tm β-2assoc))
  β-2assoc-dep-self =
    Whisk.dep-tm-wk
      (Whisk.dep-tm-wk
        (Dep.dep-var Dep.dep-refl))

  β-2assoc-dep-tgt :
    Dep.DepVarTm
      (Raw.succ (Raw.succ (Raw.succ Raw.zero)))
      (Raw-Tm (Mor₂.tm β-2assoc))
  β-2assoc-dep-tgt =
    Whisk.dep-tm-wk
      (Whisk.dep-tm-wk
        (Dep.dep-var
          (Dep.dep-ty
            (Dep.dep-tgt
              (Dep.dep-var Dep.dep-refl)))))

  γ-2assoc-dep-self :
    Dep.DepVarTm Raw.zero (Raw-Tm (Mor₂.tm γ-2assoc-cell))
  γ-2assoc-dep-self =
    Dep.dep-var Dep.dep-refl

  γ-2assoc-dep-tgt :
    Dep.DepVarTm
      (Raw.succ Raw.zero)
      (Raw-Tm (Mor₂.tm γ-2assoc-cell))
  γ-2assoc-dep-tgt =
    Dep.dep-var
      (Dep.dep-ty
        (Dep.dep-tgt
          (Dep.dep-var Dep.dep-refl)))

  assoc₂-src-dep :
    (z : Var Γ-2assoc) →
    Dep.DepVarTm z (Raw-Tm (Mor₂.tm assoc₂-src))
  assoc₂-src-dep Raw.zero =
    comp₂-dep-right
      {α₂ = γ-2assoc-cell}
      {α₁ = β-2assoc •₂ α-2assoc}
      Raw.zero
      γ-2assoc-dep-self
  assoc₂-src-dep (Raw.succ Raw.zero) =
    comp₂-dep-right
      {α₂ = γ-2assoc-cell}
      {α₁ = β-2assoc •₂ α-2assoc}
      (Raw.succ Raw.zero)
      γ-2assoc-dep-tgt
  assoc₂-src-dep (Raw.succ (Raw.succ Raw.zero)) =
    comp₂-dep-left
      {α₂ = γ-2assoc-cell}
      {α₁ = β-2assoc •₂ α-2assoc}
      (Raw.succ (Raw.succ Raw.zero))
      (comp₂-dep-right
        {α₂ = β-2assoc}
        {α₁ = α-2assoc}
        (Raw.succ (Raw.succ Raw.zero))
        β-2assoc-dep-self)
  assoc₂-src-dep (Raw.succ (Raw.succ (Raw.succ Raw.zero))) =
    comp₂-dep-left
      {α₂ = γ-2assoc-cell}
      {α₁ = β-2assoc •₂ α-2assoc}
      (Raw.succ (Raw.succ (Raw.succ Raw.zero)))
      (comp₂-dep-right
        {α₂ = β-2assoc}
        {α₁ = α-2assoc}
        (Raw.succ (Raw.succ (Raw.succ Raw.zero)))
        β-2assoc-dep-tgt)
  assoc₂-src-dep (Raw.succ (Raw.succ (Raw.succ (Raw.succ z)))) =
    comp₂-dep-left
      {α₂ = γ-2assoc-cell}
      {α₁ = β-2assoc •₂ α-2assoc}
      (Raw.succ (Raw.succ (Raw.succ (Raw.succ z))))
      (comp₂-dep-left
        {α₂ = β-2assoc}
        {α₁ = α-2assoc}
        (Raw.succ (Raw.succ (Raw.succ (Raw.succ z))))
        (α-2assoc-dep-tail z))

  assoc₂-tgt-dep :
    (z : Var Γ-2assoc) →
    Dep.DepVarTm z (Raw-Tm (Mor₂.tm assoc₂-tgt))
  assoc₂-tgt-dep Raw.zero =
    comp₂-dep-right
      {α₂ = γ-2assoc-cell •₂ β-2assoc}
      {α₁ = α-2assoc}
      Raw.zero
      (comp₂-dep-right
        {α₂ = γ-2assoc-cell}
        {α₁ = β-2assoc}
        Raw.zero
        γ-2assoc-dep-self)
  assoc₂-tgt-dep (Raw.succ Raw.zero) =
    comp₂-dep-right
      {α₂ = γ-2assoc-cell •₂ β-2assoc}
      {α₁ = α-2assoc}
      (Raw.succ Raw.zero)
      (comp₂-dep-right
        {α₂ = γ-2assoc-cell}
        {α₁ = β-2assoc}
        (Raw.succ Raw.zero)
        γ-2assoc-dep-tgt)
  assoc₂-tgt-dep (Raw.succ (Raw.succ Raw.zero)) =
    comp₂-dep-right
      {α₂ = γ-2assoc-cell •₂ β-2assoc}
      {α₁ = α-2assoc}
      (Raw.succ (Raw.succ Raw.zero))
      (comp₂-dep-left
        {α₂ = γ-2assoc-cell}
        {α₁ = β-2assoc}
        (Raw.succ (Raw.succ Raw.zero))
        β-2assoc-dep-self)
  assoc₂-tgt-dep (Raw.succ (Raw.succ (Raw.succ Raw.zero))) =
    comp₂-dep-right
      {α₂ = γ-2assoc-cell •₂ β-2assoc}
      {α₁ = α-2assoc}
      (Raw.succ (Raw.succ (Raw.succ Raw.zero)))
      (comp₂-dep-left
        {α₂ = γ-2assoc-cell}
        {α₁ = β-2assoc}
        (Raw.succ (Raw.succ (Raw.succ Raw.zero)))
        β-2assoc-dep-tgt)
  assoc₂-tgt-dep (Raw.succ (Raw.succ (Raw.succ (Raw.succ z)))) =
    comp₂-dep-left
      {α₂ = γ-2assoc-cell •₂ β-2assoc}
      {α₁ = α-2assoc}
      (Raw.succ (Raw.succ (Raw.succ (Raw.succ z))))
      (α-2assoc-dep-tail z)

opaque
  assoc₂-src-typed : HasTy (Mor₂.tm assoc₂-src) assoc₂-ty
  assoc₂-src-typed = Mor₂.hasTy assoc₂-src

opaque
  assoc₂-tgt-typed : HasTy (Mor₂.tm assoc₂-tgt) assoc₂-ty
  assoc₂-tgt-typed = Mor₂.hasTy assoc₂-tgt

opaque
  assoc₂-full :
    FullMod.Full Γ-2assoc-ps
      (Raw-Ty assoc₂-ty)
      (Raw-Tm (Mor₂.tm assoc₂-src))
      (Raw-Tm (Mor₂.tm assoc₂-tgt))
  assoc₂-full =
    FullMod.full-COMPCOH
      (λ z → assoc₂-src-dep z , assoc₂-tgt-dep z)

opaque
  assoc₂-disk-tm : Tm Γ-2assoc
  assoc₂-disk-tm =
    coh Γ-2assoc-ps assoc₂-ty
      (Mor₂.tm assoc₂-src)
      (Mor₂.tm assoc₂-tgt)
      assoc₂-src-typed
      assoc₂-tgt-typed
      assoc₂-full
      (idS Γ-2assoc)

opaque
  assoc₂-tm : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ f₄ : Mor x y}
    → (α : Mor₂ f₁ f₂) → (β : Mor₂ f₂ f₃) → (γ : Mor₂ f₃ f₄)
    → Tm Γ
  assoc₂-tm α β γ = assoc₂-disk-tm [ γ-2assoc γ β α ]t

opaque
  unfolding assoc₂-tm assoc₂-disk-tm _•₂_ comp₂-direct

  assoc₂-typed : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ f₄ : Mor x y}
    → (α : Mor₂ f₁ f₂) → (β : Mor₂ f₂ f₃) → (γ : Mor₂ f₃ f₄)
    → HasTy (assoc₂-tm α β γ)
        (homTy ([⇒] f₁ ⇒ f₄)
          (Mor₂.tm (γ •₂ (β •₂ α)))
          (Mor₂.tm ((γ •₂ β) •₂ α))
          (Mor₂.hasTy (γ •₂ (β •₂ α)))
          (Mor₂.hasTy ((γ •₂ β) •₂ α)))
  assoc₂-typed α β γ = refl

opaque
  assoc₂ : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ f₄ : Mor x y}
    → (α : Mor₂ f₁ f₂) → (β : Mor₂ f₂ f₃) → (γ : Mor₂ f₃ f₄)
    → Mor₃ (γ •₂ (β •₂ α)) ((γ •₂ β) •₂ α)
  assoc₂ α β γ = mkMor₃ (assoc₂-tm α β γ) (assoc₂-typed α β γ)

opaque
  assoc₂⁻¹ : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ f₄ : Mor x y}
    → (α : Mor₂ f₁ f₂) → (β : Mor₂ f₂ f₃) → (γ : Mor₂ f₃ f₄)
    → Mor₃ ((γ •₂ β) •₂ α) (γ •₂ (β •₂ α))
  assoc₂⁻¹ α β γ = Inv₃ (assoc₂ α β γ)

opaque
  unfolding _•₂_ comp₂-direct

  mor2-typed-•₂-raw : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y}
    → (α₂ : Mor₂ f₂ f₃) → (α₁ : Mor₂ f₁ f₂)
    → Raw-Tm (TmTyped.tm (mor2-typed (α₂ •₂ α₁)))
      ≡ Raw-Tm (TmTyped.tm (mor2-typed α₂ • mor2-typed α₁))
  mor2-typed-•₂-raw α₂ α₁ =
    cong
      (λ σ → Raw-Tm (Mor₂.tm comp₂-disk) Raw.[ σ ]t)
      (γ-2comp-rwhisk-raw-match α₂ α₁)

opaque
  unfolding _•₂_ comp₂-direct

  mor2-typed-•₂ : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y}
    → (α₂ : Mor₂ f₂ f₃) → (α₁ : Mor₂ f₁ f₂)
    → mor2-typed (α₂ •₂ α₁) ≡ mor2-typed α₂ • mor2-typed α₁
  mor2-typed-•₂ α₂ α₁ =
    TmTyped-ext (mor2-typed-•₂-raw α₂ α₁)
```

## Vertical Whiskering One Dimension Up

```agda
rwhisk₂-cell-tyᵍ : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ : Mor x y}
  → Mor₂ f₁ f₂ → Mor₂ f₁ f₂ → Ty Γ
rwhisk₂-cell-tyᵍ {x = x} {y = y} {f₁ = f₁} {f₂ = f₂} α β =
  Whisk.homTy
    (Whisk.homTy
      (MorTy (obj-typed x) (obj-typed y))
      (Mor.tm f₁)
      (Mor.tm f₂)
      (TmTyped.tp (mor-typed f₁))
      (TmTyped.tp (mor-typed f₂)))
    (Mor₂.tm α)
    (Mor₂.tm β)
    (mor-tp-whisk (mor2-typed α))
    (mor-tp-whisk (mor2-typed β))

rwhisk₂-cell-typedᵍ : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ : Mor x y}
  {α β : Mor₂ f₁ f₂} → (θ : Mor₃ α β)
  → tyOf (Mor₃.tm θ) ≡ rwhisk₂-cell-tyᵍ α β
rwhisk₂-cell-typedᵍ {α = α} {β = β} θ =
  trans
    (TmTyped.tp (mor3-typed θ))
    (Ty-ext
      {A = MorTy (mor2-typed α) (mor2-typed β)}
      {A' = rwhisk₂-cell-tyᵍ α β}
      refl)

rwhisk₂-cell-itgt : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ : Mor x y}
  → (α β : Mor₂ f₁ f₂)
  → Whisk.itgt (rwhisk₂-cell-tyᵍ α β)
      (TmTyped.tm (mor-typed f₂))
rwhisk₂-cell-itgt {f₁ = f₁} {f₂ = f₂} α β =
  Whisk.itgt-step
    (mor-tp-whisk (mor2-typed α))
    (mor-tp-whisk (mor2-typed β))
    (Whisk.itgt-base
      (TmTyped.tp (mor-typed f₁))
      (TmTyped.tp (mor-typed f₂)))

abstract
  rwhisk₂-factor-raw :
    {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y}
    → (γ : Mor₂ f₂ f₃) → (α : Mor₂ f₁ f₂)
    → Raw-Tm
        (Whisk.right-whisker-tm
          (TmTyped.tp (mor-typed f₂))
          (TmTyped.tp (mor-typed f₃))
          (TmTyped.tm (mor2-typed γ))
          (mor-tp-whisk (mor2-typed γ))
          (Whisk.itgt-base
            (TmTyped.tp (mor-typed f₁))
            (TmTyped.tp (mor-typed f₂)))
          (mor-tp-whisk (mor2-typed α)))
      ≡ Raw-Tm (TmTyped.tm (mor2-typed γ • mor2-typed α))
  rwhisk₂-factor-raw {x = x} {y = y} {f₂ = f₂} {f₃ = f₃} γ α =
    sym
      (comp-raw
        {A = MorTy (obj-typed x) (obj-typed y)}
        {y = mor-typed f₂}
        {z = mor-typed f₃}
        (mor2-typed γ)
        (mor2-typed α))

opaque
  rwhisk₂-tm : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y}
    {α β : Mor₂ f₁ f₂}
    → (γ : Mor₂ f₂ f₃) → Mor₃ α β → Tm Γ
  rwhisk₂-tm {Γ = Γ} {x = x} {y = y} {f₂ = f₂} {f₃ = f₃} {α = α} {β = β} γ θ =
    Whisk.right-whisker-tm
      {Γ = Γ}
      {B = MorTy (obj-typed x) (obj-typed y)}
      {A = rwhisk₂-cell-tyᵍ α β}
      {y = Mor.tm f₂}
      {z = Mor.tm f₃}
      (TmTyped.tp (mor-typed f₂))
      (TmTyped.tp (mor-typed f₃))
      (TmTyped.tm (mor2-typed γ))
      (mor-tp-whisk (mor2-typed γ))
      (rwhisk₂-cell-itgt α β)
      {a = Mor₃.tm θ}
      (rwhisk₂-cell-typedᵍ θ)

opaque
  unfolding rwhisk₂-tm

  rwhisk₂-typed : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y}
    {α β : Mor₂ f₁ f₂}
    → (γ : Mor₂ f₂ f₃) → (θ : Mor₃ α β)
    → HasTy (rwhisk₂-tm γ θ)
        (homTy ([⇒] f₁ ⇒ f₃)
          (Mor₂.tm (γ •₂ α))
          (Mor₂.tm (γ •₂ β))
          (Mor₂.hasTy (γ •₂ α))
          (Mor₂.hasTy (γ •₂ β)))
  rwhisk₂-typed {Γ = Γ} {x = x} {y = y} {f₁ = f₁} {f₂ = f₂} {f₃ = f₃} {α = α} {β = β} γ θ =
    tyOf≡→HasTy
      {t = rwhisk₂-tm γ θ}
      {A =
        homTy ([⇒] f₁ ⇒ f₃)
          (Mor₂.tm (γ •₂ α))
          (Mor₂.tm (γ •₂ β))
          (Mor₂.hasTy (γ •₂ α))
          (Mor₂.hasTy (γ •₂ β))}
      (trans
        (Whisk.right-whisker-tm-typed
          {Γ = Γ}
          {B = MorTy (obj-typed x) (obj-typed y)}
          {A = rwhisk₂-cell-tyᵍ α β}
          {y = Mor.tm f₂}
          {z = Mor.tm f₃}
          (TmTyped.tp (mor-typed f₂))
          (TmTyped.tp (mor-typed f₃))
          (TmTyped.tm (mor2-typed γ))
          (mor-tp-whisk (mor2-typed γ))
          (rwhisk₂-cell-itgt α β)
          {a = Mor₃.tm θ}
          (rwhisk₂-cell-typedᵍ θ))
        (Ty-ext
          (cong₂
            (λ s t →
              Raw.[ Raw-Ty ([⇒] f₁ ⇒ f₃) ] s ⇒ t)
            (sym (mor2-typed-•₂-raw γ α))
            (sym (mor2-typed-•₂-raw γ β)))))

opaque
  _∗ᵣ₂_ :
    {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y}
    {α β : Mor₂ f₁ f₂} →
    (γ : Mor₂ f₂ f₃) → Mor₃ α β →
    Mor₃ (γ •₂ α) (γ •₂ β)
  _∗ᵣ₂_ γ θ =
    mkMor₃ (rwhisk₂-tm γ θ) (rwhisk₂-typed γ θ)

postulate
  _∗ₗ₂_ :
    {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y}
    {α β : Mor₂ f₂ f₃} →
    (δ : Mor₂ f₁ f₂) → Mor₃ α β →
    Mor₃ (α •₂ δ) (β •₂ δ)
```
