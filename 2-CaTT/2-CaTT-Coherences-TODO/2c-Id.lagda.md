# 2c-Id: Identities

```agda
module 2c-Id where

import 1a-RawSyntax as Raw
import 1b-Dependency as Dep
import 1c-Pasting as Ps
import 1d-Fullness as FullMod
import 2a-CaTT-Comp as C
import 2b-Whiskering as Whisk
open import 2c-Comp public
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc; _+_; s≤s; z≤n) renaming (zero to zeroℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)
```
## Identities

The identity map `id x : x → x` is defined using the coherence of the context
`Γ-ob = (x : ⋆)`.

```agda
opaque
  id : {Γ : Ctx} {A : Ty Γ} → (x : TmTyped A) → TmTyped (MorTy x x)
  id {Γ = Γ} {A = A} (mk a pa) = mk id-tm id-typed
    where
      n : ℕ
      n = dim-ty A
      σ : Sub Γ (Whisk.Γ-disk n)
      σ = Whisk.γ-disk A a pa
      disk-cell : Tm (Whisk.Γ-disk n)
      disk-cell = var (Whisk.W.varps-to-var (Whisk.W.cell-dangling n))
      id-tm : Tm Γ
      id-tm =
        coh
          (Whisk.Γ-disk-ps n)
          (Whisk.A-disk n)
          disk-cell
          disk-cell
          refl
          refl
          (Whisk.full-id-disk n)
          σ
      id-typed : tyOf id-tm ≡ MorTy (mk a pa) (mk a pa)
      id-typed =
        Ty-ext
          (cong₂ (λ B t → Raw.[ B ] t ⇒ t)
            (Whisk.γ-disk-type-image A a pa)
            (Whisk.γ-disk-cell-image A a pa))

  id₁ : {Γ : Ctx} → (x : Obj Γ) → Mor x x
  id₁ x = typed-mor (id (obj-typed x))

  id₂-direct : {Γ : Ctx} {x y : Obj Γ} → (f : Mor x y) → Mor₂ f f
  id₂-direct {Γ = Γ} {x = x} {y = y} f = mkMor₂ id₂-tm id₂-typed
    where
      A : Ty Γ
      A = [⋆] x ⇒ y

      a : Tm Γ
      a = Mor.tm f

      pa : tyOf a ≡ A
      pa = HasTy→tyOf≡ (Mor.hasTy f)

      n : ℕ
      n = dim-ty A

      σ : Sub Γ (Whisk.Γ-disk n)
      σ = Whisk.γ-disk A a pa

      disk-cell : Tm (Whisk.Γ-disk n)
      disk-cell = var (Whisk.W.varps-to-var (Whisk.W.cell-dangling n))

      id₂-tm : Tm Γ
      id₂-tm =
        coh
          (Whisk.Γ-disk-ps n)
          (Whisk.A-disk n)
          disk-cell
          disk-cell
          refl
          refl
          (Whisk.full-id-disk n)
          σ

      id₂-typed : HasTy id₂-tm ([⇒] f ⇒ f)
      id₂-typed =
        tyOf≡→HasTy {t = id₂-tm} {A = [⇒] f ⇒ f}
          (trans
            (Ty-ext
              (cong₂ (λ B t → Raw.[ B ] t ⇒ t)
                (Whisk.γ-disk-type-image A a pa)
                (Whisk.γ-disk-cell-image A a pa)))
            (Ty-ext {A = MorTy (mk a pa) (mk a pa)} {A' = [⇒] f ⇒ f} refl))

  id₂ : {Γ : Ctx} {x y : Obj Γ} → (f : Mor x y) → Mor₂ f f
  id₂ = id₂-direct

abstract
  α-2mor-dep-all :
    (z : Var Γ-2mor) →
    Dep.DepVarTm z (Raw-Tm (Mor₂.tm α-2mor))
  α-2mor-dep-all Raw.zero =
    Dep.dep-var Dep.dep-refl
  α-2mor-dep-all (Raw.succ Raw.zero) =
    Dep.dep-var (Dep.dep-ty (Dep.dep-tgt (Dep.dep-var Dep.dep-refl)))
  α-2mor-dep-all (Raw.succ (Raw.succ Raw.zero)) =
    Dep.dep-var (Dep.dep-ty (Dep.dep-src (Dep.dep-var (Dep.dep-weak Dep.dep-refl))))
  α-2mor-dep-all (Raw.succ (Raw.succ (Raw.succ Raw.zero))) =
    Dep.dep-var
      (Dep.dep-ty
        (Dep.dep-base
          (Dep.dep-tgt
            (Dep.dep-var (Dep.dep-weak (Dep.dep-weak Dep.dep-refl))))))
  α-2mor-dep-all (Raw.succ (Raw.succ (Raw.succ (Raw.succ Raw.zero)))) =
    Dep.dep-var
      (Dep.dep-ty
        (Dep.dep-base
          (Dep.dep-src
            (Dep.dep-var (Dep.dep-weak (Dep.dep-weak (Dep.dep-weak Dep.dep-refl)))))))
  α-2mor-dep-all (Raw.succ (Raw.succ (Raw.succ (Raw.succ (Raw.succ ()))))) 

  id₃-full :
    FullMod.Full Γ-2mor-ps
      (Raw-Ty ([⇒] f₁-2mor ⇒ f₂-2mor))
      (Raw-Tm (Mor₂.tm α-2mor))
      (Raw-Tm (Mor₂.tm α-2mor))
  id₃-full =
    FullMod.full-COMPCOH
      (λ z → α-2mor-dep-all z , α-2mor-dep-all z)

  id₃-disk-tm : Tm Γ-2mor
  id₃-disk-tm =
    coh Γ-2mor-ps ([⇒] f₁-2mor ⇒ f₂-2mor)
      (Mor₂.tm α-2mor)
      (Mor₂.tm α-2mor)
      (Mor₂.hasTy α-2mor)
      (Mor₂.hasTy α-2mor)
      id₃-full
      (idS Γ-2mor)

  id₃-disk-typed :
    HasTy id₃-disk-tm
      (homTy
        ([⇒] f₁-2mor ⇒ f₂-2mor)
        (Mor₂.tm α-2mor)
        (Mor₂.tm α-2mor)
        (Mor₂.hasTy α-2mor)
        (Mor₂.hasTy α-2mor))
  id₃-disk-typed =
    coh-id-typed Γ-2mor-ps ([⇒] f₁-2mor ⇒ f₂-2mor)
      (Mor₂.tm α-2mor)
      (Mor₂.tm α-2mor)
      (Mor₂.hasTy α-2mor)
      (Mor₂.hasTy α-2mor)
      id₃-full

id₃-tm : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} → Mor₂ f g → Tm Γ
id₃-tm α = id₃-disk-tm [ γ-2mor α ]t

abstract
  id₃-typed : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) → HasTy (id₃-tm α)
      (homTy ([⇒] f ⇒ g) (Mor₂.tm α) (Mor₂.tm α) (Mor₂.hasTy α) (Mor₂.hasTy α))
  id₃-typed {f = f} {g = g} α =
    tyOf≡→HasTy
      {t = id₃-tm α}
      {A = homTy ([⇒] f ⇒ g) (Mor₂.tm α) (Mor₂.tm α) (Mor₂.hasTy α) (Mor₂.hasTy α)}
      (trans
        (tyOfSub
          {Γ = _}
          {Δ = Γ-2mor}
          {t = id₃-disk-tm}
          {A =
            homTy
              ([⇒] f₁-2mor ⇒ f₂-2mor)
              (Mor₂.tm α-2mor)
              (Mor₂.tm α-2mor)
              (Mor₂.hasTy α-2mor)
              (Mor₂.hasTy α-2mor)}
          {σ = γ-2mor α}
          (HasTy→tyOf≡
            {t = id₃-disk-tm}
            {A =
              homTy
                ([⇒] f₁-2mor ⇒ f₂-2mor)
                (Mor₂.tm α-2mor)
                (Mor₂.tm α-2mor)
                (Mor₂.hasTy α-2mor)
                (Mor₂.hasTy α-2mor)}
            id₃-disk-typed))
        (Ty-ext refl))

opaque
  id₃ : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} → (α : Mor₂ f g) → Mor₃ α α
  id₃ α = mkMor₃ (id₃-tm α) (id₃-typed α)
```
