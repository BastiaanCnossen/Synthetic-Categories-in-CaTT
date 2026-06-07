# 2c-Comp: Composites

```agda
module 2c-Comp where

import 1a-RawSyntax-Comp as Raw
import 1b-Dependency as Dep
import 1c-Pasting as Ps
import 1d-Fullness as FullMod
import 2a-CaTT-Comp as C
import 2b-Whiskering as Whisk
open import 2c-Core public
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc; _+_; s≤s; z≤n) renaming (zero to zeroℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)

infixr 30 _•_
infixr 30 _•₁_
infixr 30 _•₂ᵀ_
infixr 30 _•₂ᶜ_
infixr 30 _•₂_
infixr 30 _•₃_
```
## Composite of n-morphisms

```agda
γ-disk-cast-cell-image :
  {Γ : Ctx} {A : Ty Γ} {a : Tm Γ}
  → (k : ℕ)
  → (e : dim-ty A ≡ k)
  → (pa : tyOf a ≡ A)
  → Whisk.W.cell k Raw.[ Raw-Sub (Whisk.γ-disk-cast k e pa) ]t
    ≡ Raw-Tm a
γ-disk-cast-cell-image k refl pa =
  Whisk.γ-disk-cell-image _ _ pa

raw-γ-disk-cast-type-image :
  {Γ : Raw.RawCtx} {A : Raw.RawTy Γ} {a : Raw.RawTm Γ}
  → (k : ℕ)
  → (e : Whisk.W.dim-ty A ≡ k)
  → (dA : Whisk.W.DiskTy A)
  → (pa : Raw.tyOf a ≡ A)
  → Whisk.W.A-disk k
      Raw.[ Whisk.W.γ-disk-cast {Γ = Γ} {A = A} {a = a} k e dA pa ]T
    ≡ A
raw-γ-disk-cast-type-image {A = A} {a = a} k refl dA pa =
  Whisk.W.γ-disk-type-image {A = A} {a = a} dA pa

raw-γ-disk-cast-cell-image :
  {Γ : Raw.RawCtx} {A : Raw.RawTy Γ} {a : Raw.RawTm Γ}
  → (k : ℕ)
  → (e : Whisk.W.dim-ty A ≡ k)
  → (dA : Whisk.W.DiskTy A)
  → (pa : Raw.tyOf a ≡ A)
  → Whisk.W.cell k
      Raw.[ Whisk.W.γ-disk-cast {Γ = Γ} {A = A} {a = a} k e dA pa ]t
    ≡ a
raw-γ-disk-cast-cell-image {A = A} {a = a} k refl dA pa =
  Whisk.W.γ-disk-cell-image {A = A} {a = a} dA pa

idS-dep :
  {Γ : Ctx}
  → (x : Var Γ)
  → Dep.DepVarSub x (Raw.idS (Raw-Ctx Γ))
idS-dep {Γ = mkCtx Raw.◆ Γwf} ()
idS-dep {Γ = mkCtx (Γraw Raw.▸ Araw) (Γwf ▸wf Awf)} Raw.zero =
  Dep.dep-sub-here (Dep.dep-var Dep.dep-refl)
idS-dep {Γ = mkCtx (Γraw Raw.▸ Araw) (Γwf ▸wf Awf)} (Raw.succ x) =
  Dep.dep-sub-there
    (Whisk.dep-sub-wk (idS-dep {Γ = mkCtx Γraw Γwf} x))

comp : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A} →
  MorTm y z → MorTm x y → MorTm x z

comp-tmᵀ : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A} →
  MorTm y z → MorTm x y → Tm Γ
comp-tmᵀ {A = A} {x = mk x px} {y = mk y py} {z = mk z pz} g f =
  Whisk.right-whisker-tm
    py pz
    (TmTyped.tm g)
    (mor-tp-whisk g)
    (Whisk.itgt-base px py)
    (mor-tp-whisk f)

abstract
  comp-tyᵀ : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A} →
    (g : MorTm y z) → (f : MorTm x y) → tyOf (comp-tmᵀ g f) ≡ MorTy x z
  comp-tyᵀ {A = A} {x = mk x px} {y = mk y py} {z = mk z pz} g f =
    trans
      (Whisk.right-whisker-tm-typed
        py pz
        (TmTyped.tm g)
        (mor-tp-whisk g)
        (Whisk.itgt-base px py)
        (mor-tp-whisk f))
      (Ty-ext refl)

comp g f = mk (comp-tmᵀ g f) (comp-tyᵀ g f)

abstract
  comp-raw : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
    → (g : MorTm y z) → (f : MorTm x y)
    → Raw-Tm (TmTyped.tm (comp g f))
      ≡ Raw-Tm (Whisk.right-whisker-tm-univ (dim-ty A) 0)
          Raw.[
            Raw-Sub
              (Whisk.γ-rwhisk
                (TmTyped.tp y)
                (TmTyped.tp z)
                (mor-tp-whisk g)
                (mor-tp-whisk f)
                (Whisk.itgt-base (TmTyped.tp x) (TmTyped.tp y)))
          ]t
  comp-raw g f = refl

  comp-raw-cong-r : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
    → (g : MorTm y z) → {f f' : MorTm x y}
    → Raw-Tm (TmTyped.tm f) ≡ Raw-Tm (TmTyped.tm f')
    → Raw-Tm (TmTyped.tm (comp g f)) ≡ Raw-Tm (TmTyped.tm (comp g f'))
  comp-raw-cong-r g {f = mk (mkTm r rwf) p} {f' = mk (mkTm .r rwf') p'} refl
    with Tm-iswf-uip r rwf rwf'
  ... | refl with uip p p'
  ... | refl = refl

  comp-raw-cong-l : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
    → (f : MorTm x y) → {g g' : MorTm y z}
    → Raw-Tm (TmTyped.tm g) ≡ Raw-Tm (TmTyped.tm g')
    → Raw-Tm (TmTyped.tm (comp g f)) ≡ Raw-Tm (TmTyped.tm (comp g' f))
  comp-raw-cong-l f {g = mk (mkTm r rwf) p} {g' = mk (mkTm .r rwf') p'} refl
    with Tm-iswf-uip r rwf rwf'
  ... | refl with uip p p'
  ... | refl = refl


_•_ : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A} →
  MorTm y z → MorTm x y → MorTm x z
_•_ = comp


comp₁-tm : {Γ : Ctx} {x y z : Obj Γ} →
  Mor y z → Mor x y → Tm Γ
comp₁-tm {x = x} {y = y} {z = z} g f =
  Whisk.right-whisker-tm
    (TmTyped.tp (obj-typed y))
    (TmTyped.tp (obj-typed z))
    (TmTyped.tm (mor-typed g))
    (mor-tp-whisk (mor-typed g))
    (Whisk.itgt-base
      (TmTyped.tp (obj-typed x))
      (TmTyped.tp (obj-typed y)))
    (mor-tp-whisk (mor-typed f))

abstract
  comp₁-typed : {Γ : Ctx} {x y z : Obj Γ} →
    (g : Mor y z) (f : Mor x y) →
    HasTy (comp₁-tm g f) ([⋆] x ⇒ z)
  comp₁-typed {x = x} {y = y} {z = z} g f =
    tyOf≡→HasTy
      {t = comp₁-tm g f}
      {A = [⋆] x ⇒ z}
      (trans
        (Whisk.right-whisker-tm-typed
          (TmTyped.tp (obj-typed y))
          (TmTyped.tp (obj-typed z))
          (TmTyped.tm (mor-typed g))
          (mor-tp-whisk (mor-typed g))
          (Whisk.itgt-base
            (TmTyped.tp (obj-typed x))
            (TmTyped.tp (obj-typed y)))
          (mor-tp-whisk (mor-typed f)))
        (Ty-ext refl))

opaque
  _•₁_ : {Γ : Ctx} {x y z : Obj Γ} → Mor y z → Mor x y → Mor x z
  g •₁ f = mkMor (comp₁-tm g f) (comp₁-typed g f)

private module Comp₁Raw where
  obj-disk-sub-raw :
    {Γ Δ : Ctx} →
    (x : Obj Δ) → (σ : Sub Γ Δ) →
    Raw-Sub
      (Whisk.γ-disk-cast
        zeroℕ
        refl
        (TmTyped.tp (obj-typed x)))
      Raw.∘ Raw-Sub σ
      ≡
    Raw-Sub
      (Whisk.γ-disk-cast
        zeroℕ
        refl
        (TmTyped.tp (obj-typed (x [ σ ]obj))))
  obj-disk-sub-raw x σ = refl

  mor-disk-sub-raw :
    {Γ Δ : Ctx} {x y : Obj Δ} →
    (f : Mor x y) → (σ : Sub Γ Δ) →
    Raw-Sub
      (Whisk.γ-disk-cast
        (suc zeroℕ)
        refl
        (mor-tp-whisk (mor-typed f)))
      Raw.∘ Raw-Sub σ
      ≡
    Raw-Sub
      (Whisk.γ-disk-cast
        (suc zeroℕ)
        refl
        (mor-tp-whisk (mor-typed (f [ σ ]mor))))
  mor-disk-sub-raw {x = x} {y = y} f σ =
    trans
      (cong
        (λ δ → δ Raw.∘ Raw-Sub σ)
        (Whisk.γ-disk-cast-hom-raw
          (TmTyped.tp (obj-typed x))
          (TmTyped.tp (obj-typed y))
          (mor-tp-whisk (mor-typed f))
          zeroℕ
          refl))
      (trans
        (cong
          (λ δ →
            Raw.⟨
              Raw.⟨
                δ
              , Raw-Tm (Obj.tm y) Raw.[ Raw-Sub σ ]t
              ⟩
            , Raw-Tm (Mor.tm f) Raw.[ Raw-Sub σ ]t
            ⟩)
          (obj-disk-sub-raw x σ))
        (sym
          (Whisk.γ-disk-cast-hom-raw
            (TmTyped.tp (obj-typed (x [ σ ]obj)))
            (TmTyped.tp (obj-typed (y [ σ ]obj)))
            (mor-tp-whisk (mor-typed (f [ σ ]mor)))
            zeroℕ
            refl)))

  comp₁-γ :
    {Γ : Ctx} {x y z : Obj Γ} →
    (g : Mor y z) → (f : Mor x y) →
    Sub Γ (Whisk.Γ-rwhisk zeroℕ zeroℕ)
  comp₁-γ {x = x} {y = y} {z = z} g f =
    Whisk.γ-rwhisk
      (TmTyped.tp (obj-typed y))
      (TmTyped.tp (obj-typed z))
      (mor-tp-whisk (mor-typed g))
      (mor-tp-whisk (mor-typed f))
      (Whisk.itgt-base
        (TmTyped.tp (obj-typed x))
        (TmTyped.tp (obj-typed y)))

  comp₁-γ-raw-match :
    {Γ : Ctx} {x y z : Obj Γ} →
    (g : Mor y z) → (f : Mor x y) →
    Raw-Sub (comp₁-γ g f)
      ≡
    Raw.⟨
      Raw.⟨
        Raw-Sub
          (Whisk.γ-disk-cast
            (suc zeroℕ)
            refl
            (mor-tp-whisk (mor-typed f)))
      , Raw-Tm (Obj.tm z)
      ⟩
    , Raw-Tm (Mor.tm g)
    ⟩
  comp₁-γ-raw-match {x = x} {y = y} {z = z} g f =
    cong
      (λ e →
        Raw.⟨
          Raw.⟨
            Raw-Sub
              (Whisk.γ-disk-cast
                (suc zeroℕ)
                e
                (mor-tp-whisk (mor-typed f)))
          , Raw-Tm (Obj.tm z)
          ⟩
        , Raw-Tm (Mor.tm g)
        ⟩)
      (uip
        (Whisk.itgt-dim
          (TmTyped.tp (obj-typed y))
          (Whisk.itgt-base
            (TmTyped.tp (obj-typed x))
            (TmTyped.tp (obj-typed y))))
        refl)

  obj-disk-raw-match :
    {Γ : Ctx} →
    (x : Obj Γ) →
    Raw-Sub
      (Whisk.γ-disk-cast
        zeroℕ
        refl
        (TmTyped.tp (obj-typed x)))
      ≡
    Raw.⟨ Raw.◆S , Raw-Tm (Obj.tm x) ⟩
  obj-disk-raw-match x = refl

  obj-disk-raw-cong :
    {Γ : Ctx} →
    (x x' : Obj Γ) →
    Raw-Tm (Obj.tm x) ≡ Raw-Tm (Obj.tm x') →
    Raw-Sub
      (Whisk.γ-disk-cast
        zeroℕ
        refl
        (TmTyped.tp (obj-typed x)))
      ≡
    Raw-Sub
      (Whisk.γ-disk-cast
        zeroℕ
        refl
        (TmTyped.tp (obj-typed x')))
  obj-disk-raw-cong x x' px =
    trans
      (obj-disk-raw-match x)
      (trans
        (cong (λ u → Raw.⟨ Raw.◆S , u ⟩) px)
        (sym (obj-disk-raw-match x')))

  mor-disk-raw-cong :
    {Γ : Ctx} {x y x' y' : Obj Γ} →
    (f : Mor x y) → (f' : Mor x' y') →
    Raw-Tm (Obj.tm x) ≡ Raw-Tm (Obj.tm x') →
    Raw-Tm (Obj.tm y) ≡ Raw-Tm (Obj.tm y') →
    Raw-Tm (Mor.tm f) ≡ Raw-Tm (Mor.tm f') →
    Raw-Sub
      (Whisk.γ-disk-cast
        (suc zeroℕ)
        refl
        (mor-tp-whisk (mor-typed f)))
      ≡
    Raw-Sub
      (Whisk.γ-disk-cast
        (suc zeroℕ)
        refl
        (mor-tp-whisk (mor-typed f')))
  mor-disk-raw-cong {x = x} {y = y} {x' = x'} {y' = y'} f f' px py pf =
    trans
      (Whisk.γ-disk-cast-hom-raw
        (TmTyped.tp (obj-typed x))
        (TmTyped.tp (obj-typed y))
        (mor-tp-whisk (mor-typed f))
        zeroℕ
        refl)
      (trans
        (cong
          (λ δ →
            Raw.⟨
              Raw.⟨
                δ
              , Raw-Tm (Obj.tm y)
              ⟩
            , Raw-Tm (Mor.tm f)
            ⟩)
          (obj-disk-raw-cong x x' px))
        (trans
          (cong
            (λ v →
              Raw.⟨
                Raw.⟨
                  Raw-Sub
                    (Whisk.γ-disk-cast
                      zeroℕ
                      refl
                      (TmTyped.tp (obj-typed x')))
                , v
                ⟩
              , Raw-Tm (Mor.tm f)
              ⟩)
            py)
          (trans
            (cong
              (λ a →
                Raw.⟨
                  Raw.⟨
                    Raw-Sub
                      (Whisk.γ-disk-cast
                        zeroℕ
                        refl
                        (TmTyped.tp (obj-typed x')))
                  , Raw-Tm (Obj.tm y')
                  ⟩
                , a
                ⟩)
              pf)
            (sym
              (Whisk.γ-disk-cast-hom-raw
                (TmTyped.tp (obj-typed x'))
                (TmTyped.tp (obj-typed y'))
                (mor-tp-whisk (mor-typed f'))
                zeroℕ
                refl)))))

  comp₁-γ-raw-cong :
    {Γ : Ctx} {x y z x' y' z' : Obj Γ} →
    (g : Mor y z) → (f : Mor x y) →
    (g' : Mor y' z') → (f' : Mor x' y') →
    Raw-Tm (Obj.tm x) ≡ Raw-Tm (Obj.tm x') →
    Raw-Tm (Obj.tm y) ≡ Raw-Tm (Obj.tm y') →
    Raw-Tm (Obj.tm z) ≡ Raw-Tm (Obj.tm z') →
    Raw-Tm (Mor.tm g) ≡ Raw-Tm (Mor.tm g') →
    Raw-Tm (Mor.tm f) ≡ Raw-Tm (Mor.tm f') →
    Raw-Sub (comp₁-γ g f)
      ≡
    Raw-Sub (comp₁-γ g' f')
  comp₁-γ-raw-cong {x = x} {y = y} {z = z} {x' = x'} {y' = y'} {z' = z'}
      g f g' f' px py pz pg pf =
    trans
      (comp₁-γ-raw-match g f)
      (trans
        (cong
          (λ δ →
            Raw.⟨
              Raw.⟨
                δ
              , Raw-Tm (Obj.tm z)
              ⟩
            , Raw-Tm (Mor.tm g)
            ⟩)
          (mor-disk-raw-cong f f' px py pf))
        (trans
          (cong
            (λ v →
              Raw.⟨
                Raw.⟨
                  Raw-Sub
                    (Whisk.γ-disk-cast
                      (suc zeroℕ)
                      refl
                      (mor-tp-whisk (mor-typed f')))
                , v
                ⟩
              , Raw-Tm (Mor.tm g)
              ⟩)
            pz)
          (trans
            (cong
              (λ a →
                Raw.⟨
                  Raw.⟨
                    Raw-Sub
                      (Whisk.γ-disk-cast
                        (suc zeroℕ)
                        refl
                        (mor-tp-whisk (mor-typed f')))
                  , Raw-Tm (Obj.tm z')
                  ⟩
                , a
                ⟩)
              pg)
            (sym (comp₁-γ-raw-match g' f')))))

  comp₁-γ-sub-raw :
    {Γ Δ : Ctx} {x y z : Obj Δ} →
    (g : Mor y z) → (f : Mor x y) → (σ : Sub Γ Δ) →
    Raw-Sub (comp₁-γ g f) Raw.∘ Raw-Sub σ
      ≡
    Raw-Sub (comp₁-γ (g [ σ ]mor) (f [ σ ]mor))
  comp₁-γ-sub-raw {x = x} {y = y} {z = z} g f σ =
    trans
      (cong
        (λ δ → δ Raw.∘ Raw-Sub σ)
        (comp₁-γ-raw-match g f))
      (trans
        (cong
          (λ δ →
            Raw.⟨
              Raw.⟨
                δ
              , Raw-Tm (Obj.tm z) Raw.[ Raw-Sub σ ]t
              ⟩
            , Raw-Tm (Mor.tm g) Raw.[ Raw-Sub σ ]t
            ⟩)
          (mor-disk-sub-raw f σ))
        (sym (comp₁-γ-raw-match (g [ σ ]mor) (f [ σ ]mor))))

  opaque
    unfolding _•₁_

    comp₁-raw-match :
      {Γ : Ctx} {x y z : Obj Γ} →
      (g : Mor y z) → (f : Mor x y) →
      Raw-Tm (Mor.tm (g •₁ f))
        ≡
      Raw-Tm (Whisk.right-whisker-tm-univ zeroℕ zeroℕ)
        Raw.[ Raw-Sub (comp₁-γ g f) ]t
    comp₁-raw-match g f = refl

abstract
  comp₁-sub-raw-image :
    {Γ Δ : Ctx} {x y z : Obj Δ} →
    (g : Mor y z) → (f : Mor x y) → (σ : Sub Γ Δ) →
    Raw-Tm (Mor.tm ((g •₁ f) [ σ ]mor))
      ≡
    Raw-Tm (Mor.tm ((g [ σ ]mor) •₁ (f [ σ ]mor)))
  comp₁-sub-raw-image g f σ =
    trans
      (cong
        (λ t → t Raw.[ Raw-Sub σ ]t)
        (Comp₁Raw.comp₁-raw-match g f))
      (trans
        (sym
          (Raw.[∘]t
            (Raw-Tm (Whisk.right-whisker-tm-univ zeroℕ zeroℕ))
            (Raw-Sub (Comp₁Raw.comp₁-γ g f))
            (Raw-Sub σ)))
        (trans
          (cong
            (λ δ →
              Raw-Tm (Whisk.right-whisker-tm-univ zeroℕ zeroℕ)
                Raw.[ δ ]t)
            (Comp₁Raw.comp₁-γ-sub-raw g f σ))
          (sym (Comp₁Raw.comp₁-raw-match (g [ σ ]mor) (f [ σ ]mor)))))

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
  comp₁-raw-cong g f g' f' px py pz pg pf =
    trans
      (Comp₁Raw.comp₁-raw-match g f)
      (trans
        (cong
          (λ δ →
            Raw-Tm (Whisk.right-whisker-tm-univ zeroℕ zeroℕ)
              Raw.[ δ ]t)
          (Comp₁Raw.comp₁-γ-raw-cong g f g' f' px py pz pg pf))
        (sym (Comp₁Raw.comp₁-raw-match g' f')))
```


## Object-Level Whiskering Contexts

The whiskering coherences below still use the compact object-level telescopes
from the original construction. The actual composites are the typed-layer
composites defined above.

```agda
Γ-ob : Ctx
Γ-ob = ◆ ▸ ⋆

x-ob : Tm Γ-ob
x-ob = var (zero {Γ = ◆} {A = ⋆})

x-ob-obj : Obj Γ-ob
x-ob-obj = mkObj x-ob refl

γ-ob : {Γ : Ctx} → Obj Γ → Sub Γ Γ-ob
γ-ob x = ⟨ ◆S , Obj.tm x ⟩:[ HasTy→tyOf≡ (Obj.hasTy x) ]

abstract
  γ-ob-disk-raw-match :
    {Γ : Ctx} → (x : Obj Γ) →
    Raw-Sub (γ-ob x)
    ≡
    Raw-Sub
      (Whisk.γ-disk-cast
        zeroℕ
        refl
        (TmTyped.tp (obj-typed x)))
  γ-ob-disk-raw-match x = refl

Γ-ob² : Ctx
Γ-ob² = Γ-ob ▸ ⋆

y-ob² : Obj Γ-ob²
y-ob² = mkObj (var (zero {Γ = Γ-ob} {A = ⋆})) refl

x-ob² : Obj Γ-ob²
x-ob² = x-ob-obj [ wk ]obj

ty-f : Ty Γ-ob²
ty-f = [⋆] x-ob² ⇒ y-ob²

Γ-mor : Ctx
Γ-mor = Γ-ob² ▸ ty-f

wk-ob² : Sub Γ-mor Γ-ob
wk-ob² = wk {Γ = Γ-ob} {A = ⋆} ∘ wk {Γ = Γ-ob²} {A = ty-f}

x-mor : Obj Γ-mor
x-mor = x-ob-obj [ wk-ob² ]obj

y-mor : Obj Γ-mor
y-mor = y-ob² [ wk {A = ty-f} ]obj

f-mor : Mor x-mor y-mor
f-mor = mkMor (var (zero {Γ = Γ-ob²} {A = ty-f})) refl

γ-ob² : {Γ : Ctx} → (x y : Obj Γ) → Sub Γ Γ-ob²
γ-ob² x y = ⟨ γ-ob x , Obj.tm y ⟩:[ HasTy→tyOf≡ (Obj.hasTy y) ]

ty-f-image : {Γ : Ctx} (x y : Obj Γ) →
    ty-f [ γ-ob² x y ]T ≡ [⋆] x ⇒ y
ty-f-image x y = Ty-ext refl

abstract
  γ-mor-typed : {Γ : Ctx} {x y : Obj Γ} (f : Mor x y) →
    tyOf (Mor.tm f) ≡ ty-f [ γ-ob² x y ]T
  γ-mor-typed {x = x} {y = y} f =
    trans (HasTy→tyOf≡ (Mor.hasTy f)) (sym (ty-f-image x y))

γ-mor : {Γ : Ctx} {x y : Obj Γ} → Mor x y → Sub Γ Γ-mor
γ-mor {x = x} {y = y} f = ⟨ γ-ob² x y , Mor.tm f ⟩:[ γ-mor-typed f ]

abstract
  γ-mor-disk-raw-match :
    {Γ : Ctx} {x y : Obj Γ} → (f : Mor x y) →
    Raw-Sub (γ-mor f)
    ≡
    Raw-Sub
      (Whisk.γ-disk-cast
        (suc zeroℕ)
        refl
        (mor-tp-whisk (mor-typed f)))
  γ-mor-disk-raw-match {x = x} {y = y} f =
    trans
      refl
      (sym
        (trans
          (Whisk.γ-disk-cast-hom-raw
            (TmTyped.tp (obj-typed x))
            (TmTyped.tp (obj-typed y))
            (mor-tp-whisk (mor-typed f))
            zeroℕ
            refl)
          (cong
            (λ σ → Raw.⟨ Raw.⟨ σ , Raw-Tm (Obj.tm y) ⟩ , Raw-Tm (Mor.tm f) ⟩)
            (sym (γ-ob-disk-raw-match x)))))

Γ-mor-ob : Ctx
Γ-mor-ob = Γ-mor ▸ ⋆

z-mor-ob : Obj Γ-mor-ob
z-mor-ob = mkObj (var (zero {Γ = Γ-mor} {A = ⋆})) refl

y-mor-ob : Obj Γ-mor-ob
y-mor-ob = y-mor [ wk ]obj

ty-g : Ty Γ-mor-ob
ty-g = [⋆] y-mor-ob ⇒ z-mor-ob

Γ-comp : Ctx
Γ-comp = Γ-mor-ob ▸ ty-g

Γ-comp-ps : Ps.CtxPs (Raw-Ctx Γ-comp)
Γ-comp-ps = Ps.ps-ext (Ps.varps-y Ps.varps-ob)

x-comp : Obj Γ-comp
x-comp = x-mor [ wk ]obj [ wk ]obj

y-comp : Obj Γ-comp
y-comp = y-mor [ wk ]obj [ wk ]obj

z-comp : Obj Γ-comp
z-comp = z-mor-ob [ wk ]obj

f-comp : Mor x-comp y-comp
f-comp = f-mor [ wk ]mor [ wk ]mor

g-comp : Mor y-comp z-comp
g-comp = mkMor (var (zero {Γ = Γ-mor-ob} {A = ty-g})) refl

γ-mor-ob : {Γ : Ctx} {x y : Obj Γ} → Mor x y → Obj Γ → Sub Γ Γ-mor-ob
γ-mor-ob f z = ⟨ γ-mor f , Obj.tm z ⟩:[ HasTy→tyOf≡ (Obj.hasTy z) ]

ty-g-image : {Γ : Ctx} {x y z : Obj Γ} (f : Mor x y) →
    ty-g [ γ-mor-ob f z ]T ≡ [⋆] y ⇒ z
ty-g-image f = Ty-ext refl

abstract
  γ-comp-typed : {Γ : Ctx} {x y z : Obj Γ} (g : Mor y z) (f : Mor x y) →
    tyOf (Mor.tm g) ≡ ty-g [ γ-mor-ob f z ]T
  γ-comp-typed g f =
    trans (HasTy→tyOf≡ (Mor.hasTy g)) (sym (ty-g-image f))

γ-comp : {Γ : Ctx} {x y z : Obj Γ} → Mor y z → Mor x y → Sub Γ Γ-comp
γ-comp {z = z} g f = ⟨ γ-mor-ob f z , Mor.tm g ⟩:[ γ-comp-typed g f ]

mor-ty-mor : Ty Γ-mor
mor-ty-mor = [⋆] x-mor ⇒ y-mor

Γ-mor² : Ctx
Γ-mor² = Γ-mor ▸ mor-ty-mor

x-mor² : Obj Γ-mor²
x-mor² = x-mor [ wk ]obj

y-mor² : Obj Γ-mor²
y-mor² = y-mor [ wk ]obj

f₂-mor² : Mor x-mor² y-mor²
f₂-mor² = mkMor (var (zero {Γ = Γ-mor} {A = mor-ty-mor})) refl

ty-α : Ty Γ-mor²
ty-α = [⇒] (f-mor [ wk ]mor) ⇒ f₂-mor²

Γ-2mor : Ctx
Γ-2mor = Γ-mor² ▸ ty-α

Γ-2mor-ps : Ps.CtxPs (Raw-Ctx Γ-2mor)
Γ-2mor-ps = Ps.ps-ext (Ps.varps-f Ps.varps-ob)

x-2mor : Obj Γ-2mor
x-2mor = x-mor² [ wk ]obj

y-2mor : Obj Γ-2mor
y-2mor = y-mor² [ wk ]obj

f₁-2mor : Mor x-2mor y-2mor
f₁-2mor = f-mor [ wk ]mor [ wk ]mor

f₂-2mor : Mor x-2mor y-2mor
f₂-2mor = f₂-mor² [ wk ]mor

α-2mor : Mor₂ f₁-2mor f₂-2mor
α-2mor = mkMor₂ (var (zero {Γ = Γ-mor²} {A = ty-α})) refl

γ-mor² : {Γ : Ctx} {x y : Obj Γ} → (f₁ f₂ : Mor x y) → Sub Γ Γ-mor²
γ-mor² f₁ f₂ = ⟨ γ-mor f₁ , Mor.tm f₂ ⟩:[ HasTy→tyOf≡ (Mor.hasTy f₂) ]

ty-α-image : {Γ : Ctx} {x y : Obj Γ} → (f₁ f₂ : Mor x y) →
    ty-α [ γ-mor² f₁ f₂ ]T ≡ [⇒] f₁ ⇒ f₂
ty-α-image f₁ f₂ = Ty-ext refl

abstract
  γ-2mor-typed : {Γ : Ctx} {x y : Obj Γ} → {f₁ f₂ : Mor x y} → (α : Mor₂ f₁ f₂) →
    tyOf (Mor₂.tm α) ≡ ty-α [ γ-mor² f₁ f₂ ]T
  γ-2mor-typed {f₁ = f₁} {f₂ = f₂} α =
    trans (HasTy→tyOf≡ (Mor₂.hasTy α)) (sym (ty-α-image f₁ f₂))

γ-2mor : {Γ : Ctx} {x y : Obj Γ} → {f₁ f₂ : Mor x y} → Mor₂ f₁ f₂ → Sub Γ Γ-2mor
γ-2mor {f₁ = f₁} {f₂ = f₂} α =
  ⟨ γ-mor² f₁ f₂ , Mor₂.tm α ⟩:[ γ-2mor-typed α ]

abstract
  γ-2mor-disk-raw-match :
    {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ : Mor x y} → (α : Mor₂ f₁ f₂) →
    Raw-Sub (γ-2mor α)
    ≡
    Raw-Sub
      (Whisk.γ-disk-cast
        (suc (suc zeroℕ))
        refl
        (mor-tp-whisk (mor2-typed α)))
  γ-2mor-disk-raw-match {f₁ = f₁} {f₂ = f₂} α =
    trans
      refl
      (sym
        (trans
          (Whisk.γ-disk-cast-hom-raw
            (TmTyped.tp (mor-typed f₁))
            (TmTyped.tp (mor-typed f₂))
            (mor-tp-whisk (mor2-typed α))
            (suc zeroℕ)
            refl)
          (cong
            (λ σ → Raw.⟨ Raw.⟨ σ , Raw-Tm (Mor.tm f₂) ⟩ , Raw-Tm (Mor₂.tm α) ⟩)
            (sym (γ-mor-disk-raw-match f₁)))))

f₂-2mor-ps : VarPs Γ-2mor Γ-2mor-ps
f₂-2mor-ps = Ps.varps-y (Ps.varps-f Ps.varps-ob)

f₃-2comp-ty : Ty Γ-2mor
f₃-2comp-ty = varps-to-type f₂-2mor-ps

Γ-2comp-mor : Ctx
Γ-2comp-mor = Γ-2mor ▸ f₃-2comp-ty

β-2comp-ty : Ty Γ-2comp-mor
β-2comp-ty =
  [ wkTy f₃-2comp-ty ]
    vs (Ps.varps-to-var f₂-2mor-ps) ⇒ vz :[ refl , refl ]

Γ-2comp : Ctx
Γ-2comp = Γ-2comp-mor ▸ β-2comp-ty

Γ-2comp-ps : CtxPs Γ-2comp
Γ-2comp-ps = Ps.ps-ext f₂-2mor-ps

wk-2comp-mor : Sub Γ-2comp-mor Γ-2mor
wk-2comp-mor = wk {Γ = Γ-2mor} {A = f₃-2comp-ty}

wk-2comp : Sub Γ-2comp Γ-2comp-mor
wk-2comp = wk {Γ = Γ-2comp-mor} {A = β-2comp-ty}

x-2comp : Obj Γ-2comp
x-2comp = x-2mor [ wk-2comp-mor ]obj [ wk-2comp ]obj

y-2comp : Obj Γ-2comp
y-2comp = y-2mor [ wk-2comp-mor ]obj [ wk-2comp ]obj

f₁-2comp : Mor x-2comp y-2comp
f₁-2comp = f₁-2mor [ wk-2comp-mor ]mor [ wk-2comp ]mor

f₂-2comp : Mor x-2comp y-2comp
f₂-2comp = f₂-2mor [ wk-2comp-mor ]mor [ wk-2comp ]mor

f₃-2comp : Mor x-2comp y-2comp
f₃-2comp =
  mkMor
    (var (succ {Γ = Γ-2comp-mor} {A = β-2comp-ty}
      (zero {Γ = Γ-2mor} {A = f₃-2comp-ty})))
    refl

α₁-2comp : Mor₂ f₁-2comp f₂-2comp
α₁-2comp = mkMor₂ (Mor₂.tm α-2mor [ wk-2comp-mor ]t [ wk-2comp ]t) refl

α₂-2comp : Mor₂ f₂-2comp f₃-2comp
α₂-2comp =
  mkMor₂ (var (zero {Γ = Γ-2comp-mor} {A = β-2comp-ty})) refl

comp₂-base-ty : Ty Γ-2comp
comp₂-base-ty = [⋆] x-2comp ⇒ y-2comp

comp₂-full :
  FullMod.Full Γ-2comp-ps
    (Raw-Ty comp₂-base-ty)
    (Raw-Tm (Mor.tm f₁-2comp))
    (Raw-Tm (Mor.tm f₃-2comp))
comp₂-full = Whisk.comp-full (suc zeroℕ)

comp₂-disk-tm : Tm Γ-2comp
comp₂-disk-tm =
  coh Γ-2comp-ps comp₂-base-ty
    (Mor.tm f₁-2comp)
    (Mor.tm f₃-2comp)
    (Mor.hasTy f₁-2comp)
    (Mor.hasTy f₃-2comp)
    comp₂-full
    (idS Γ-2comp)

comp₂-disk-typed : HasTy comp₂-disk-tm ([⇒] f₁-2comp ⇒ f₃-2comp)
comp₂-disk-typed =
  coh-id-typed Γ-2comp-ps comp₂-base-ty
    (Mor.tm f₁-2comp)
    (Mor.tm f₃-2comp)
    (Mor.hasTy f₁-2comp)
    (Mor.hasTy f₃-2comp)
    comp₂-full

comp₂-disk : Mor₂ f₁-2comp f₃-2comp
comp₂-disk = mkMor₂ comp₂-disk-tm comp₂-disk-typed

comp₂-mor-ty-image :
  {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ : Mor x y} →
  (α₁ : Mor₂ f₁ f₂) →
  varps-to-type f₂-2mor-ps [ γ-2mor α₁ ]T ≡ [⋆] x ⇒ y
comp₂-mor-ty-image α₁ = Ty-ext refl

comp₂-mor-typed :
  {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
  (α₁ : Mor₂ f₁ f₂) →
  tyOf (Mor.tm f₃) ≡ varps-to-type f₂-2mor-ps [ γ-2mor α₁ ]T
comp₂-mor-typed {f₃ = f₃} α₁ =
  trans (HasTy→tyOf≡ (Mor.hasTy f₃)) (sym (comp₂-mor-ty-image α₁))

γ-2comp-mor :
  {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
  (α₁ : Mor₂ f₁ f₂) → Sub Γ Γ-2comp-mor
γ-2comp-mor {f₃ = f₃} α₁ =
  ⟨ γ-2mor α₁ , Mor.tm f₃ ⟩:[ comp₂-mor-typed {f₃ = f₃} α₁ ]

comp₂-α₂-ty-image :
  {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
  (α₂ : Mor₂ f₂ f₃) (α₁ : Mor₂ f₁ f₂) →
  β-2comp-ty [ γ-2comp-mor {f₃ = f₃} α₁ ]T
  ≡ [⇒] f₂ ⇒ f₃
comp₂-α₂-ty-image α₂ α₁ = Ty-ext refl

comp₂-α₂-typed-raw :
  {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
  (α₂ : Mor₂ f₂ f₃) (α₁ : Mor₂ f₁ f₂) →
  Raw.tyOf (Raw-Tm (Mor₂.tm α₂))
    ≡
  Raw-Ty β-2comp-ty
    Raw.[ Raw-Sub (γ-2comp-mor {f₃ = f₃} α₁) ]T
comp₂-α₂-typed-raw α₂ α₁ =
  trans
    (Mor₂.hasTy α₂)
    (cong Raw-Ty (sym (comp₂-α₂-ty-image α₂ α₁)))

γ-2comp :
  {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
  Mor₂ f₂ f₃ → Mor₂ f₁ f₂ → Sub Γ Γ-2comp
γ-2comp {f₃ = f₃} α₂ α₁ =
  ⟨ γ-2comp-mor {f₃ = f₃} α₁ , Mor₂.tm α₂ ⟩∶[
    comp₂-α₂-typed-raw α₂ α₁ ]

abstract
  γ-2comp-rwhisk-raw-match :
    {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y}
    → (α₂ : Mor₂ f₂ f₃) → (α₁ : Mor₂ f₁ f₂)
    → Raw-Sub (γ-2comp α₂ α₁)
      ≡
      Raw-Sub
        (Whisk.γ-rwhisk
          (TmTyped.tp (mor-typed f₂))
          (TmTyped.tp (mor-typed f₃))
          (mor-tp-whisk (mor2-typed α₂))
          (mor-tp-whisk (mor2-typed α₁))
          (Whisk.itgt-base
            (TmTyped.tp (mor-typed f₁))
            (TmTyped.tp (mor-typed f₂))))
  γ-2comp-rwhisk-raw-match {f₁ = f₁} {f₂ = f₂} {f₃ = f₃} α₂ α₁ =
    trans
      (cong
        (λ σ → Raw.⟨ Raw.⟨ σ , Raw-Tm (Mor.tm f₃) ⟩ , Raw-Tm (Mor₂.tm α₂) ⟩)
        (γ-2mor-disk-raw-match α₁))
      (cong
        (λ e →
          Raw.⟨
            Raw.⟨
              Raw-Sub
                (Whisk.γ-disk-cast
                  (suc (suc zeroℕ))
                  e
                  (mor-tp-whisk (mor2-typed α₁)))
            , Raw-Tm (Mor.tm f₃) ⟩
          , Raw-Tm (Mor₂.tm α₂) ⟩)
        (uip
          refl
          (Whisk.itgt-dim
            (TmTyped.tp (mor-typed f₂))
            (Whisk.itgt-base
              (TmTyped.tp (mor-typed f₁))
              (TmTyped.tp (mor-typed f₂))))))

comp₂-tm :
  {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
  Mor₂ f₂ f₃ → Mor₂ f₁ f₂ → Tm Γ
comp₂-tm α₂ α₁ = Mor₂.tm comp₂-disk [ γ-2comp α₂ α₁ ]t

comp₂-type-image :
  {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
  (α₂ : Mor₂ f₂ f₃) (α₁ : Mor₂ f₁ f₂) →
  ([⇒] f₁-2comp ⇒ f₃-2comp) [ γ-2comp α₂ α₁ ]T
  ≡ [⇒] f₁ ⇒ f₃
comp₂-type-image α₂ α₁ = Ty-ext refl

comp₂-typed :
  {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
  (α₂ : Mor₂ f₂ f₃) (α₁ : Mor₂ f₁ f₂) →
  HasTy (comp₂-tm α₂ α₁) ([⇒] f₁ ⇒ f₃)
comp₂-typed α₂ α₁ =
  trans
    (tmSub-typed
      {t = Mor₂.tm comp₂-disk}
      {A = [⇒] f₁-2comp ⇒ f₃-2comp}
      {σ = γ-2comp α₂ α₁}
      (Mor₂.hasTy comp₂-disk))
    (cong Raw-Ty (comp₂-type-image α₂ α₁))

opaque
  comp₂-direct : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
    Mor₂ f₂ f₃ → Mor₂ f₁ f₂ → Mor₂ f₁ f₃
  comp₂-direct α₂ α₁ = mkMor₂ (comp₂-tm α₂ α₁) (comp₂-typed α₂ α₁)

  _•₂ᶜ_ : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
    Mor₂ f₂ f₃ → Mor₂ f₁ f₂ → Mor₂ f₁ f₃
  _•₂ᶜ_ = comp₂-direct

  _•₂ᵀ_ : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
    MorTm (mor-typed f₂) (mor-typed f₃) →
    MorTm (mor-typed f₁) (mor-typed f₂) →
    MorTm (mor-typed f₁) (mor-typed f₃)
  α₂ •₂ᵀ α₁ = mor2-typed (comp₂-direct (typed-mor2 α₂) (typed-mor2 α₁))

  _•₂_ : {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y} →
    Mor₂ f₂ f₃ → Mor₂ f₁ f₂ → Mor₂ f₁ f₃
  _•₂_ = comp₂-direct

opaque
  unfolding _•₂_ comp₂-direct

  comp₂-dep-left :
    {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y}
    → {α₂ : Mor₂ f₂ f₃} {α₁ : Mor₂ f₁ f₂}
    → (z : Var Γ)
    → Dep.DepVarTm z (Raw-Tm (Mor₂.tm α₁))
    → Dep.DepVarTm z (Raw-Tm (Mor₂.tm (α₂ •₂ α₁)))
  comp₂-dep-left {α₂ = α₂} {α₁ = α₁} z d =
    Dep.dep-coh
      (subst
        (Dep.DepVarSub z)
        (sym (Raw.∘-idS-l (Raw-Sub (γ-2comp α₂ α₁))))
        (Dep.dep-sub-there
          (Dep.dep-sub-there
            (Dep.dep-sub-here d))))

  comp₂-dep-right :
    {Γ : Ctx} {x y : Obj Γ} {f₁ f₂ f₃ : Mor x y}
    → {α₂ : Mor₂ f₂ f₃} {α₁ : Mor₂ f₁ f₂}
    → (z : Var Γ)
    → Dep.DepVarTm z (Raw-Tm (Mor₂.tm α₂))
    → Dep.DepVarTm z (Raw-Tm (Mor₂.tm (α₂ •₂ α₁)))
  comp₂-dep-right {α₂ = α₂} {α₁ = α₁} z d =
    Dep.dep-coh
      (subst
        (Dep.DepVarSub z)
        (sym (Raw.∘-idS-l (Raw-Sub (γ-2comp α₂ α₁))))
        (Dep.dep-sub-here d))

opaque
  _•₃_ : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} {α β γ : Mor₂ f g} →
    Mor₃ β γ → Mor₃ α β → Mor₃ α γ
  Θ₂ •₃ Θ₁ = typed-mor3 (mor3-typed Θ₂ • mor3-typed Θ₁)

```
