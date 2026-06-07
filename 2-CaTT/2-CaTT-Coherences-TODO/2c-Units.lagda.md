# 2c-Units: Unit Coherences

```agda
module 2c-Units where

import 1a-RawSyntax-Comp as Raw
import 1b-Dependency as Dep
import 1c-Pasting as Ps
import 1d-Fullness as FullMod
import 2a-CaTT-Comp as C
import 2b-Whiskering as Whisk
open import 2c-Id public
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc; _+_; s≤s; z≤n) renaming (zero to zeroℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)
```
## Unit Laws

```agda
lunit : {Γ : Ctx} {A : Ty Γ} {x y : TmTyped A} → (f : MorTm x y) → MorTm (id y • f) f
lunit {Γ = Γ} {A = A} {x = x} {y = y} f = mk lunit-tm lunit-typed
  where
    n : ℕ
    n = dim-ty A

    Δ : Ctx
    Δ = Whisk.Γ-disk (suc n)

    B : Ty Δ
    B = Whisk.disk-endpoint-ty n

    xᵈ : TmTyped B
    xᵈ = mk {A = B} (Whisk.disk-src n)
      (HasTy→tyOf≡ {t = Whisk.disk-src n} {A = B} refl)

    yᵈ : TmTyped B
    yᵈ = mk {A = B} (Whisk.disk-tgt n)
      (HasTy→tyOf≡ {t = Whisk.disk-tgt n} {A = B} refl)

    fᵈ-tm : Tm Δ
    fᵈ-tm = var {Γ = Δ} (Whisk.W.varps-to-var (Whisk.W.cell-dangling (suc n)))

    fᵈ-ty : tyOf fᵈ-tm ≡ MorTy xᵈ yᵈ
    fᵈ-ty =
      trans
        (HasTy→tyOf≡ {t = fᵈ-tm} {A = Whisk.A-disk (suc n)} refl)
        (Ty-ext refl)

    fᵈ : MorTm xᵈ yᵈ
    fᵈ = mk {A = MorTy xᵈ yᵈ} fᵈ-tm fᵈ-ty

    δᵈ : Sub Δ (Whisk.Γ-disk n)
    δᵈ = mkSub (Whisk.W.disk-prev-tgt-raw n) (Whisk.disk-prev-tgt-raw-iswf n)

    disk-cellᵈ : Tm (Whisk.Γ-disk n)
    disk-cellᵈ = var (Whisk.W.varps-to-var (Whisk.W.cell-dangling n))

    δᵈ-type-image :
      Raw-Ty (Whisk.A-disk n) Raw.[ Raw-Sub δᵈ ]T
      ≡ Raw-Ty B
    δᵈ-type-image =
      raw-γ-disk-cast-type-image
        {A = Whisk.W.disk-endpoint-ty n}
        {a = Whisk.W.disk-tgt n}
        n
        (Whisk.W.dim-disk-endpoint-ty n)
        (Whisk.W.disk-endpoint-diskTy n)
        refl

    δᵈ-cell-image :
      Raw-Tm disk-cellᵈ Raw.[ Raw-Sub δᵈ ]t
      ≡ Raw-Tm (TmTyped.tm yᵈ)
    δᵈ-cell-image =
      raw-γ-disk-cast-cell-image
        {A = Whisk.W.disk-endpoint-ty n}
        {a = Whisk.W.disk-tgt n}
        n
        (Whisk.W.dim-disk-endpoint-ty n)
        (Whisk.W.disk-endpoint-diskTy n)
        refl

    idᵈ-tm : Tm Δ
    idᵈ-tm =
      coh
        (Whisk.Γ-disk-ps n)
        (Whisk.A-disk n)
        disk-cellᵈ
        disk-cellᵈ
        refl
        refl
        (Whisk.full-id-disk n)
        δᵈ

    idᵈ-typed : tyOf idᵈ-tm ≡ MorTy yᵈ yᵈ
    idᵈ-typed =
      Ty-ext
        (cong₂
          (λ A₀ t → Raw.[ A₀ ] t ⇒ t)
          δᵈ-type-image
          δᵈ-cell-image)

    idᵈ : MorTm yᵈ yᵈ
    idᵈ = mk idᵈ-tm idᵈ-typed

    σ : Sub Γ Δ
    σ = Whisk.γ-disk-cast (suc n) refl (mor-tp-whisk f)

    midᵈ : Ty Δ
    midᵈ = varps-to-type (Whisk.W.rwhisk-mid n 0)

    midHomᵈ : Ty (Δ ▸ midᵈ)
    midHomᵈ =
      [ wkTy midᵈ ]
        vs (Whisk.W.varps-to-var (Whisk.W.rwhisk-mid n 0))
        ⇒ vz :[ refl , refl ]

    γ-srcᵈ-simple-inner =
      ⟨_,_⟩:[_]
        (idS Δ)
        {A = midᵈ}
        (TmTyped.tm yᵈ)
        (trans (TmTyped.tp yᵈ) (trans (Ty-ext refl) (sym ([]T-id midᵈ))))

    midHomᵈ-image : midHomᵈ [ γ-srcᵈ-simple-inner ]T ≡ MorTy yᵈ yᵈ
    midHomᵈ-image =
      Ty-ext
        (Whisk.ext-cell-ty-snoc-raw
          (Whisk.W.rwhisk-mid n 0)
          (Raw.lookup-idS (Whisk.W.varps-to-var (Whisk.W.rwhisk-mid n 0)))
          (Raw.[idS]T (Raw-Ty midᵈ)))

    γ-srcᵈ-simple0 =
      ⟨_,_⟩:[_]
        γ-srcᵈ-simple-inner
        {A = midHomᵈ}
        (TmTyped.tm idᵈ)
        (trans (TmTyped.tp idᵈ) (sym midHomᵈ-image))

    γ-srcᵈ-simple : Sub Δ (Whisk.Γ-rwhisk n 0)
    γ-srcᵈ-simple =
      mkSub (Raw-Sub γ-srcᵈ-simple0) (Sub-wf γ-srcᵈ-simple0)

    lunit-srcᵈ-simple-tm : Tm Δ
    lunit-srcᵈ-simple-tm =
      Whisk.right-whisker-tm-univ n 0 [ γ-srcᵈ-simple ]t

    simple-comp-ty-image :
      Whisk.W.Γ-comp-ty-raw n Raw.[ Raw-Sub γ-srcᵈ-simple ]T
      ≡ Raw-Ty B
    simple-comp-ty-image =
      trans
        (cong
          (λ A₀ → A₀ Raw.[ Raw-Sub γ-srcᵈ-simple ]T)
          (Whisk.W.Γ-comp-ty-raw-match n))
        (trans
          (Raw.wkTy-[]T
            (Raw.wkTy (Raw-Ty midᵈ))
            (Raw-Sub γ-srcᵈ-simple-inner)
            (Raw-Tm (TmTyped.tm idᵈ)))
          (trans
            (Raw.wkTy-[]T
              (Raw-Ty midᵈ)
              (Raw.idS (Raw-Ctx Δ))
              (Raw-Tm (TmTyped.tm yᵈ)))
            (Raw.[idS]T (Raw-Ty midᵈ))))

    simple-comp-src-image :
      Whisk.W.Γ-comp-src-raw n Raw.[ Raw-Sub γ-srcᵈ-simple ]t
      ≡ Raw-Tm (TmTyped.tm xᵈ)
    simple-comp-src-image =
      trans
        (cong
          (λ t → t Raw.[ Raw-Sub γ-srcᵈ-simple ]t)
          (Whisk.W.Γ-comp-src-raw-match n))
        (Raw.lookup-idS (Whisk.W.disk-src-var n))

    simple-comp-tgt-image :
      Whisk.W.Γ-comp-tgt-raw n Raw.[ Raw-Sub γ-srcᵈ-simple ]t
      ≡ Raw-Tm (TmTyped.tm yᵈ)
    simple-comp-tgt-image =
      trans
        (cong
          (λ t → t Raw.[ Raw-Sub γ-srcᵈ-simple ]t)
          (Whisk.W.Γ-comp-tgt-raw-match n))
        refl

    simple-rwhisk-type-image :
      Raw-Ty (Whisk.right-whisker-ty-univ n 0 [ γ-srcᵈ-simple ]T)
      ≡ Raw-Ty (MorTy xᵈ yᵈ)
    simple-rwhisk-type-image =
      trans
        (cong
          (λ A₀ → A₀ Raw.[ Raw-Sub γ-srcᵈ-simple ]T)
          (Whisk.right-whisker-ty-univ0-raw n))
        (trans
          (cong
            (λ A₀ → A₀ Raw.[ Raw-Sub γ-srcᵈ-simple ]T)
            (Whisk.W.Γ-comp-univ-ty-raw-match n))
          (trans
            (cong
              (λ A₀ →
                Raw.[ A₀ ]
                  (Whisk.W.Γ-comp-src-raw n Raw.[ Raw-Sub γ-srcᵈ-simple ]t)
                  ⇒
                  (Whisk.W.Γ-comp-tgt-raw n Raw.[ Raw-Sub γ-srcᵈ-simple ]t))
              simple-comp-ty-image)
            (trans
              (cong
                (λ s →
                  Raw.[ Raw-Ty B ]
                    s
                    ⇒
                    (Whisk.W.Γ-comp-tgt-raw n Raw.[ Raw-Sub γ-srcᵈ-simple ]t))
                simple-comp-src-image)
              (cong
                (λ t →
                  Raw.[ Raw-Ty B ]
                    (Raw-Tm (TmTyped.tm xᵈ))
                    ⇒ t)
                simple-comp-tgt-image))))

    lunit-srcᵈ-simple-ty : tyOf lunit-srcᵈ-simple-tm ≡ MorTy xᵈ yᵈ
    lunit-srcᵈ-simple-ty =
      trans
        (tyOfSub
          {t = Whisk.right-whisker-tm-univ n 0}
          {A = Whisk.right-whisker-ty-univ n 0}
          {σ = γ-srcᵈ-simple}
          (Whisk.right-whisker-tm-typed-univ n 0))
        (Ty-ext simple-rwhisk-type-image)

    lunit-srcᵈ : MorTm xᵈ yᵈ
    lunit-srcᵈ = mk lunit-srcᵈ-simple-tm lunit-srcᵈ-simple-ty

    lunit-src-dep :
      (z : Var Δ)
      → Dep.DepVarTm z (Raw-Tm (TmTyped.tm lunit-srcᵈ))
    lunit-src-dep z =
      Dep.dep-coh
        (subst
          (Dep.DepVarSub z)
          (sym (Raw.∘-idS-l (Raw-Sub γ-srcᵈ-simple)))
          (Dep.dep-sub-there
            (Dep.dep-sub-there
              (idS-dep {Γ = Δ} z))))

    lunit-tgt-dep :
      (z : Var Δ)
      → Dep.DepVarTm z (Raw-Tm fᵈ-tm)
    lunit-tgt-dep z =
      Dep.dep-var (Whisk.disk-dangling-all (suc n) z)

    lunit-full :
      FullMod.Full
        (Whisk.Γ-disk-ps (suc n))
        (Raw-Ty (MorTy xᵈ yᵈ))
        (Raw-Tm (TmTyped.tm lunit-srcᵈ))
        (Raw-Tm fᵈ-tm)
    lunit-full =
      FullMod.full-COMPCOH
        (λ z → lunit-src-dep z , lunit-tgt-dep z)

    lunit-tm : Tm Γ
    lunit-tm =
      coh
        (Whisk.Γ-disk-ps (suc n))
        (MorTy xᵈ yᵈ)
        (TmTyped.tm lunit-srcᵈ)
        fᵈ-tm
        (tyOf≡→HasTy {t = TmTyped.tm lunit-srcᵈ} {A = MorTy xᵈ yᵈ}
          (TmTyped.tp lunit-srcᵈ))
        (tyOf≡→HasTy {t = fᵈ-tm} {A = MorTy xᵈ yᵈ} fᵈ-ty)
        lunit-full
        σ

    lunit-base-image :
      Raw-Ty (MorTy xᵈ yᵈ) Raw.[ Raw-Sub σ ]T
      ≡ Raw-Ty (MorTy x y)
    lunit-base-image =
      trans
        (Whisk.γ-disk-cast-type-image (suc n) refl (mor-tp-whisk f))
        refl

    lunit-tgt-image :
      Raw-Tm fᵈ-tm Raw.[ Raw-Sub σ ]t
      ≡ Raw-Tm (TmTyped.tm f)
    lunit-tgt-image =
      γ-disk-cast-cell-image (suc n) refl (mor-tp-whisk f)

    idʸ : MorTm y y
    idʸ = id {A = A} y

    q :
      Whisk.itgt
        (Whisk.homTy A
          (TmTyped.tm x)
          (TmTyped.tm y)
          (TmTyped.tp x)
          (TmTyped.tp y))
        (TmTyped.tm y)
    q = Whisk.itgt-base (TmTyped.tp x) (TmTyped.tp y)

    γ-src : Sub Γ (Whisk.Γ-rwhisk n 0)
    γ-src =
      Whisk.γ-rwhisk
        {B = A}
        {A =
          Whisk.homTy A
            (TmTyped.tm x)
            (TmTyped.tm y)
            (TmTyped.tp x)
            (TmTyped.tp y)}
        {y = TmTyped.tm y}
        {z = TmTyped.tm y}
        {a = TmTyped.tm f}
        {g = TmTyped.tm idʸ}
        (TmTyped.tp y)
        (TmTyped.tp y)
        (mor-tp-whisk idʸ)
        (mor-tp-whisk f)
        q

    σ-cast-uip :
      Raw-Sub σ
      ≡
      Raw-Sub
        (Whisk.γ-disk-cast
          (suc n)
          (Whisk.itgt-dim (TmTyped.tp y) q)
          (mor-tp-whisk f))
    σ-cast-uip =
      cong
        (λ e →
          Raw-Sub
            (Whisk.γ-disk-cast
              (suc n)
              e
              (mor-tp-whisk f)))
        (uip refl (Whisk.itgt-dim (TmTyped.tp y) q))

    yᵈ-sub-image :
      Raw-Tm (TmTyped.tm yᵈ) Raw.[ Raw-Sub σ ]t
      ≡ Raw-Tm (TmTyped.tm y)
    yᵈ-sub-image =
      Whisk.γ-disk-cast-tgt-image
        (TmTyped.tp x)
        (TmTyped.tp y)
        (mor-tp-whisk f)

    δᵈ-σ-comp :
      Raw-Sub δᵈ Raw.∘ Raw-Sub σ
      ≡ Raw-Sub (Whisk.γ-disk-cast n refl (TmTyped.tp y))
    δᵈ-σ-comp =
      Whisk.γ-disk-tgt-comp
        (TmTyped.tp x)
        (TmTyped.tp y)
        (mor-tp-whisk f)
        n
        refl

    opaque
      unfolding id

      idᵈ-sub-image :
        Raw-Tm (TmTyped.tm idᵈ) Raw.[ Raw-Sub σ ]t
        ≡ Raw-Tm (TmTyped.tm idʸ)
      idᵈ-sub-image =
        cong
          (Raw.coh
            (Raw-Ty (Whisk.A-disk n))
            (Raw-Tm disk-cellᵈ)
            (Raw-Tm disk-cellᵈ))
          δᵈ-σ-comp

    γ-src-simple-comp :
      Raw-Sub γ-srcᵈ-simple Raw.∘ Raw-Sub σ
      ≡ Raw-Sub γ-src
    γ-src-simple-comp =
      cong₂
        Raw.⟨_,_⟩
        (cong₂
          Raw.⟨_,_⟩
          (trans (Raw.∘-idS-l (Raw-Sub σ)) σ-cast-uip)
          yᵈ-sub-image)
        idᵈ-sub-image

    lunit-src-image :
      Raw-Tm (TmTyped.tm lunit-srcᵈ) Raw.[ Raw-Sub σ ]t
      ≡ Raw-Tm (TmTyped.tm (id y • f))
    lunit-src-image =
      trans
        (sym
          (Raw.[∘]t
            (Raw-Tm (Whisk.right-whisker-tm-univ n 0))
            (Raw-Sub γ-srcᵈ-simple)
            (Raw-Sub σ)))
        (cong
          (λ τ → Raw-Tm (Whisk.right-whisker-tm-univ n 0) Raw.[ τ ]t)
          γ-src-simple-comp)

    lunit-type-image :
      Raw-Ty (tyOf lunit-tm)
      ≡ Raw-Ty (MorTy (id y • f) f)
    lunit-type-image =
      trans
        (cong
          (λ A₀ →
            Raw.[ A₀ ]
              (Raw-Tm (TmTyped.tm lunit-srcᵈ) Raw.[ Raw-Sub σ ]t)
              ⇒ (Raw-Tm fᵈ-tm Raw.[ Raw-Sub σ ]t))
          lunit-base-image)
        (trans
          (cong
            (λ s →
              Raw.[ Raw-Ty (MorTy x y) ]
                s
                ⇒ (Raw-Tm fᵈ-tm Raw.[ Raw-Sub σ ]t))
            lunit-src-image)
          (cong
            (λ t →
              Raw.[ Raw-Ty (MorTy x y) ]
                (Raw-Tm (TmTyped.tm (id y • f)))
                ⇒ t)
            lunit-tgt-image))

    lunit-typed : tyOf lunit-tm ≡ MorTy (id y • f) f
    lunit-typed = Ty-ext lunit-type-image
  
opaque
  unfolding id id₁ _•₁_

  lunit₁-src : {Γ : Ctx} {x y : Obj Γ} → (f : Mor x y) →
    mor-typed (id₁ y •₁ f) ≡ id (obj-typed y) • mor-typed f
  lunit₁-src f = TmTyped-ext refl
  

opaque
  lunit₁ : {Γ : Ctx} {x y : Obj Γ} → (f : Mor x y) → Mor₂ (id₁ y •₁ f) f
  lunit₁ f =
    typed-mor2
      (subst (λ h → MorTm h (mor-typed f))
        (sym (lunit₁-src f))
        (lunit (mor-typed f)))
```

```agda
postulate
  runit : {Γ : Ctx} {A : Ty Γ} {x y : TmTyped A} → (f : MorTm x y) → MorTm (f • id x) f

opaque
  lunit-opaque : {Γ : Ctx} {A : Ty Γ} {x y : TmTyped A} → (f : MorTm x y) → MorTm (id y • f) f
  lunit-opaque = lunit

  runit-opaque : {Γ : Ctx} {A : Ty Γ} {x y : TmTyped A} → (f : MorTm x y) → MorTm (f • id x) f
  runit-opaque = runit
```
