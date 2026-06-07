# 2c-Inv: Inverses

```agda
module 2c-Inv where

import 1a-RawSyntax-Comp as Raw
import 1b-Dependency as Dep
import 1c-Pasting as Ps
import 1d-Fullness as FullMod
import 2a-CaTT-Comp as C
import 2b-Whiskering as Whisk
open import 2c-Id public
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _<_; s≤s; z≤n) renaming (zero to zeroℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)
```
## Inverse Coherences

```agda
disc-src-tm-match :
  FullMod.AllVar (Raw-Ctx Γ-2mor)
    (λ z →
      Dep.DepVarTm z (Raw-Tm (Mor.tm f₁-2mor))
      FullMod.↔
      FullMod.SrcBdry Γ-2mor-ps z)
disc-src-tm-match z = record
  { to = λ d →
      FullMod._↔_.to
        (Whisk.disk-src-var-match (suc zeroℕ) z)
        (Whisk.dep-var-tm-inv d)
  ; from = λ p →
      Dep.dep-var
        (FullMod._↔_.from
          (Whisk.disk-src-var-match (suc zeroℕ) z)
          p)
  }

disc-tgt-tm-match :
  FullMod.AllVar (Raw-Ctx Γ-2mor)
    (λ z →
      Dep.DepVarTm z (Raw-Tm (Mor.tm f₂-2mor))
      FullMod.↔
      FullMod.TgtBdry Γ-2mor-ps z)
disc-tgt-tm-match z = record
  { to = λ d →
      FullMod._↔_.to
        (Whisk.disk-tgt-var-match (suc zeroℕ) z)
        (Whisk.dep-var-tm-inv d)
  ; from = λ p →
      Dep.dep-var
        (FullMod._↔_.from
          (Whisk.disk-tgt-var-match (suc zeroℕ) z)
          p)
  }

disc-src-bdry-match :
  FullMod.AllVar (Raw-Ctx Γ-2mor)
    (λ z →
      FullMod.SrcBdry Γ-2mor-ps z
      FullMod.↔
      Dep.DepVarTm z (Raw-Tm (Mor.tm f₁-2mor)))
disc-src-bdry-match z = record
  { to = FullMod._↔_.from (disc-src-tm-match z)
  ; from = FullMod._↔_.to (disc-src-tm-match z)
  }

disc-tgt-bdry-match :
  FullMod.AllVar (Raw-Ctx Γ-2mor)
    (λ z →
      FullMod.TgtBdry Γ-2mor-ps z
      FullMod.↔
      Dep.DepVarTm z (Raw-Tm (Mor.tm f₂-2mor)))
disc-tgt-bdry-match z = record
  { to = FullMod._↔_.from (disc-tgt-tm-match z)
  ; from = FullMod._↔_.to (disc-tgt-tm-match z)
  }

inv₂-base-ty : Ty Γ-2mor
inv₂-base-ty = [⋆] x-2mor ⇒ y-2mor

inv₂-full :
  FullMod.Full Γ-2mor-ps
    (Raw-Ty inv₂-base-ty)
    (Raw-Tm (Mor.tm f₂-2mor))
    (Raw-Tm (Mor.tm f₁-2mor))
inv₂-full =
  FullMod.full-INV
    (s≤s z≤n)
    record
      { tgt-match = disc-tgt-tm-match
      ; src-match = disc-src-tm-match
      }

inv₂-disk-tm : Tm Γ-2mor
inv₂-disk-tm =
  coh Γ-2mor-ps inv₂-base-ty
    (Mor.tm f₂-2mor)
    (Mor.tm f₁-2mor)
    (Mor.hasTy f₂-2mor)
    (Mor.hasTy f₁-2mor)
    inv₂-full
    (idS Γ-2mor)

inv₂-disk-typed : HasTy inv₂-disk-tm ([⇒] f₂-2mor ⇒ f₁-2mor)
inv₂-disk-typed =
  coh-id-typed Γ-2mor-ps inv₂-base-ty
    (Mor.tm f₂-2mor)
    (Mor.tm f₁-2mor)
    (Mor.hasTy f₂-2mor)
    (Mor.hasTy f₁-2mor)
    inv₂-full

inv₂-disk : Mor₂ f₂-2mor f₁-2mor
inv₂-disk = mkMor₂ inv₂-disk-tm inv₂-disk-typed

inv₂-tm : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} → Mor₂ f g → Tm Γ
inv₂-tm α = Mor₂.tm inv₂-disk [ γ-2mor α ]t

inv₂-typed :
  {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
  (α : Mor₂ f g) → HasTy (inv₂-tm α) ([⇒] g ⇒ f)
inv₂-typed {f = f} {g = g} α =
  tyOf≡→HasTy {t = inv₂-tm α} {A = [⇒] g ⇒ f}
    (trans
      (tyOfSub
        {t = Mor₂.tm inv₂-disk}
        {A = [⇒] f₂-2mor ⇒ f₁-2mor}
        {σ = γ-2mor α}
        (HasTy→tyOf≡
          {t = Mor₂.tm inv₂-disk}
          {A = [⇒] f₂-2mor ⇒ f₁-2mor}
          (Mor₂.hasTy inv₂-disk)))
      (Ty-ext refl))

opaque
  inv₂ : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} → Mor₂ f g → Mor₂ g f
  inv₂ α = mkMor₂ (inv₂-tm α) (inv₂-typed α)

abstract
  disk-boundary-dim :
    (n : ℕ) →
    dim-ctx (Whisk.Γ-disk (suc n)) ∸ suc zeroℕ ≡ n
  disk-boundary-dim n =
    cong (λ k → k ∸ suc zeroℕ) (Whisk.dim-ctx-disk (suc n))

  disk-src-tm-match :
    (n : ℕ) →
    FullMod.AllVar (Raw-Ctx (Whisk.Γ-disk (suc n)))
      (λ z →
        Dep.DepVarTm z (Raw-Tm (Whisk.disk-src n))
        FullMod.↔
        FullMod.SrcBdry (Whisk.Γ-disk-ps (suc n)) z)
  disk-src-tm-match n z = record
    { to = λ d →
        subst
          (λ i → FullMod.SrcBdryI (Whisk.Γ-disk-ps (suc n)) z i)
          (sym (disk-boundary-dim n))
          (FullMod._↔_.to
            (Whisk.disk-src-var-match n z)
            (Whisk.dep-var-tm-inv d))
    ; from = λ p →
        Dep.dep-var
          (FullMod._↔_.from
            (Whisk.disk-src-var-match n z)
            (subst
              (λ i → FullMod.SrcBdryI (Whisk.Γ-disk-ps (suc n)) z i)
              (disk-boundary-dim n)
              p))
    }

  disk-tgt-tm-match :
    (n : ℕ) →
    FullMod.AllVar (Raw-Ctx (Whisk.Γ-disk (suc n)))
      (λ z →
        Dep.DepVarTm z (Raw-Tm (Whisk.disk-tgt n))
        FullMod.↔
        FullMod.TgtBdry (Whisk.Γ-disk-ps (suc n)) z)
  disk-tgt-tm-match n z = record
    { to = λ d →
        subst
          (λ i → FullMod.TgtBdryI (Whisk.Γ-disk-ps (suc n)) z i)
          (sym (disk-boundary-dim n))
          (FullMod._↔_.to
            (Whisk.disk-tgt-var-match n z)
            (Whisk.dep-var-tm-inv d))
    ; from = λ p →
        Dep.dep-var
          (FullMod._↔_.from
            (Whisk.disk-tgt-var-match n z)
            (subst
              (λ i → FullMod.TgtBdryI (Whisk.Γ-disk-ps (suc n)) z i)
              (disk-boundary-dim n)
              p))
    }

  inv-fullᵀ : (n : ℕ) →
    zeroℕ < dim-ty (Whisk.disk-endpoint-ty n) →
    FullMod.Full (Whisk.Γ-disk-ps (suc n))
      (Raw-Ty (Whisk.disk-endpoint-ty n))
      (Raw-Tm (Whisk.disk-tgt n))
      (Raw-Tm (Whisk.disk-src n))
  inv-fullᵀ n positive =
    FullMod.full-INV
      positive
      record
        { tgt-match = disk-tgt-tm-match n
        ; src-match = disk-src-tm-match n
        }

  inv-disk-tm : (n : ℕ) →
    zeroℕ < dim-ty (Whisk.disk-endpoint-ty n) →
    Tm (Whisk.Γ-disk (suc n))
  inv-disk-tm n positive =
    coh (Whisk.Γ-disk-ps (suc n)) (Whisk.disk-endpoint-ty n)
      (Whisk.disk-tgt n)
      (Whisk.disk-src n)
      refl
      refl
      (inv-fullᵀ n positive)
      (idS (Whisk.Γ-disk (suc n)))

  inv-disk-typed : (n : ℕ) →
    (positive : zeroℕ < dim-ty (Whisk.disk-endpoint-ty n)) →
    HasTy (inv-disk-tm n positive)
      (homTy (Whisk.disk-endpoint-ty n)
        (Whisk.disk-tgt n)
        (Whisk.disk-src n)
        refl
        refl)
  inv-disk-typed n positive =
    coh-id-typed (Whisk.Γ-disk-ps (suc n)) (Whisk.disk-endpoint-ty n)
      (Whisk.disk-tgt n)
      (Whisk.disk-src n)
      refl
      refl
      (inv-fullᵀ n positive)

  inv⁺ : {Γ : Ctx} {A : Ty Γ} {x y : TmTyped A} →
    zeroℕ < dim-ty A →
    MorTm x y → MorTm y x
  inv⁺ {Γ = Γ} {A = A} {x = mk x px} {y = mk y py} positive f =
    mk inv-tm inv-typed
    where
      n : ℕ
      n = dim-ty A

      positive-disk : zeroℕ < dim-ty (Whisk.disk-endpoint-ty n)
      positive-disk =
        subst (λ k → zeroℕ < k) (sym (Whisk.dim-disk-endpoint-ty n)) positive

      f-typed-whisk : tyOf (TmTyped.tm f) ≡ Whisk.homTy A x y px py
      f-typed-whisk =
        trans (TmTyped.tp f)
          (Ty-ext
            {A = MorTy (mk x px) (mk y py)}
            {A' = Whisk.homTy A x y px py}
            refl)

      σ : Sub Γ (Whisk.Γ-disk (suc n))
      σ =
        Whisk.γ-disk-cast
          {A = Whisk.homTy A x y px py}
          (suc n)
          refl
          f-typed-whisk

      inv-tm : Tm Γ
      inv-tm = inv-disk-tm n positive-disk [ σ ]t

      disk-src-image :
        Raw-Tm (Whisk.disk-src n) Raw.[ Raw-Sub σ ]t
          ≡ Raw-Tm x
      disk-src-image =
        Whisk.γ-disk-cast-src-image px py f-typed-whisk

      disk-tgt-image :
        Raw-Tm (Whisk.disk-tgt n) Raw.[ Raw-Sub σ ]t
          ≡ Raw-Tm y
      disk-tgt-image =
        Whisk.γ-disk-cast-tgt-image px py f-typed-whisk

      disk-endpoint-image :
        Raw-Ty (Whisk.disk-endpoint-ty n) Raw.[ Raw-Sub σ ]T
          ≡ Raw-Ty A
      disk-endpoint-image =
        trans
          (sym
            (tyOf-comm
              (Raw-Tm (Whisk.disk-src n))
              (Raw-Ty (Whisk.disk-endpoint-ty n))
              (cast-sub σ)
              refl))
          (trans
            (cong Raw.tyOf disk-src-image)
            (trans
              (tyOf-from-tyOf x)
              (cong Raw-Ty px)))

      inv-type-image :
        (homTy (Whisk.disk-endpoint-ty n)
          (Whisk.disk-tgt n)
          (Whisk.disk-src n)
          refl
          refl) [ σ ]T
        ≡ MorTy (mk y py) (mk x px)
      inv-type-image =
        Ty-ext
          (trans
            (cong
              (λ B →
                Raw.[ B ]
                  (Raw-Tm (Whisk.disk-tgt n) Raw.[ Raw-Sub σ ]t)
                  ⇒
                  (Raw-Tm (Whisk.disk-src n) Raw.[ Raw-Sub σ ]t))
              disk-endpoint-image)
            (trans
              (cong
                (λ t →
                  Raw.[ Raw-Ty A ] t ⇒
                  (Raw-Tm (Whisk.disk-src n) Raw.[ Raw-Sub σ ]t))
                disk-tgt-image)
              (cong
                (λ s → Raw.[ Raw-Ty A ] Raw-Tm y ⇒ s)
                disk-src-image)))

      inv-typed : tyOf inv-tm ≡ MorTy (mk y py) (mk x px)
      inv-typed =
        trans
          (tyOfSub
            {Γ = Γ}
            {Δ = Whisk.Γ-disk (suc n)}
            {t = inv-disk-tm n positive-disk}
            {A =
              homTy (Whisk.disk-endpoint-ty n)
                (Whisk.disk-tgt n)
                (Whisk.disk-src n)
                refl
                refl}
            {σ = σ}
            (HasTy→tyOf≡
              {t = inv-disk-tm n positive-disk}
              {A =
                homTy (Whisk.disk-endpoint-ty n)
                  (Whisk.disk-tgt n)
                  (Whisk.disk-src n)
                  refl
                  refl}
              (inv-disk-typed n positive-disk)))
          inv-type-image

  Inv₃ : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} {α β : Mor₂ f g} →
    Mor₃ α β → Mor₃ β α
  Inv₃ θ = typed-mor3 (inv⁺ (s≤s z≤n) (mor3-typed θ))

opaque
  f₁-2morᵀ : TmTyped (MorTy (obj-typed x-2mor) (obj-typed y-2mor))
  f₁-2morᵀ = mor-typed f₁-2mor

  f₂-2morᵀ : TmTyped (MorTy (obj-typed x-2mor) (obj-typed y-2mor))
  f₂-2morᵀ = mor-typed f₂-2mor

  α-2morᵀ : MorTm f₁-2morᵀ f₂-2morᵀ
  α-2morᵀ = mor2-typed α-2mor

  inv₂-α-2morᵀ : MorTm f₂-2morᵀ f₁-2morᵀ
  inv₂-α-2morᵀ = mor2-typed inv₂-disk

opaque
  inv₂-sec-ty : Ty Γ-2mor
  inv₂-sec-ty = MorTy f₂-2morᵀ f₂-2morᵀ

opaque
  unfolding f₂-2morᵀ

  inv₂-sec-lhsᵀ : MorTm f₂-2morᵀ f₂-2morᵀ
  inv₂-sec-lhsᵀ = mor2-typed (α-2mor •₂ inv₂-disk)

opaque
  unfolding f₂-2morᵀ

  inv₂-sec-rhsᵀ : MorTm f₂-2morᵀ f₂-2morᵀ
  inv₂-sec-rhsᵀ = mor2-typed (id₂ f₂-2mor)

opaque
  unfolding inv₂-sec-ty

  inv₂-sec-lhs-typed : HasTy (TmTyped.tm inv₂-sec-lhsᵀ) inv₂-sec-ty
  inv₂-sec-lhs-typed =
    tyOf≡→HasTy (TmTyped.tp inv₂-sec-lhsᵀ)

opaque
  unfolding inv₂-sec-ty

  inv₂-sec-rhs-typed : HasTy (TmTyped.tm inv₂-sec-rhsᵀ) inv₂-sec-ty
  inv₂-sec-rhs-typed =
    tyOf≡→HasTy (TmTyped.tp inv₂-sec-rhsᵀ)

opaque
  unfolding f₂-2morᵀ inv₂-sec-ty inv₂-sec-lhsᵀ inv₂-sec-rhsᵀ

  inv₂-sec-full :
    FullMod.Full Γ-2mor-ps
      (Raw-Ty inv₂-sec-ty)
      (Raw-Tm (TmTyped.tm inv₂-sec-lhsᵀ))
      (Raw-Tm (TmTyped.tm inv₂-sec-rhsᵀ))
  inv₂-sec-full =
    FullMod.full-INVCOH+
      record
        { positive-dim = s≤s (s≤s z≤n)
        ; src-match = disc-tgt-bdry-match
        ; tgt-match = disc-tgt-bdry-match
        }

opaque
  inv₂-is-sec-tm :
    {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) → Tm Γ
  inv₂-is-sec-tm α =
    coh Γ-2mor-ps inv₂-sec-ty
      (TmTyped.tm inv₂-sec-lhsᵀ)
      (TmTyped.tm inv₂-sec-rhsᵀ)
      inv₂-sec-lhs-typed
      inv₂-sec-rhs-typed
      inv₂-sec-full
      (γ-2mor α)

opaque
  unfolding α-2morᵀ

  inv₂-sec-α-image :
    {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) →
    TmTyped.tm α-2morᵀ [ γ-2mor α ]t ≡ Mor₂.tm α
  inv₂-sec-α-image α = Tm-ext refl

opaque
  unfolding inv₂-α-2morᵀ inv₂

  inv₂-sec-inv-image :
    {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) →
    TmTyped.tm inv₂-α-2morᵀ [ γ-2mor α ]t ≡ Mor₂.tm (inv₂ α)
  inv₂-sec-inv-image α = Tm-ext refl

opaque
  unfolding inv₂-sec-rhsᵀ id₂ id₂-direct

  inv₂-sec-rhs-image :
    {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) →
    TmTyped.tm inv₂-sec-rhsᵀ [ γ-2mor α ]t ≡ Mor₂.tm (id₂ g)
  inv₂-sec-rhs-image α = Tm-ext refl

opaque
  unfolding inv₂-is-sec-tm inv₂-sec-ty inv₂-sec-lhsᵀ inv₂-sec-rhsᵀ _•₂_ comp₂-direct id₂ id₂-direct inv₂

  inv₂-is-sec-typed :
    {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) →
    HasTy (inv₂-is-sec-tm α)
        (homTy ([⇒] g ⇒ g)
        (Mor₂.tm (α •₂ inv₂ α))
        (Mor₂.tm (id₂ g))
        (Mor₂.hasTy (α •₂ inv₂ α))
        (Mor₂.hasTy (id₂ g)))
  inv₂-is-sec-typed α = refl

opaque
  inv₂-is-sec : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} → (α : Mor₂ f g)
    → Mor₃ (α •₂ (inv₂ α)) (id₂ g)
  inv₂-is-sec α = mkMor₃ (inv₂-is-sec-tm α) (inv₂-is-sec-typed α)

opaque
  inv₂-ret-ty : Ty Γ-2mor
  inv₂-ret-ty = MorTy f₁-2morᵀ f₁-2morᵀ

opaque
  unfolding f₁-2morᵀ

  inv₂-ret-lhsᵀ : MorTm f₁-2morᵀ f₁-2morᵀ
  inv₂-ret-lhsᵀ = mor2-typed (inv₂-disk •₂ α-2mor)

opaque
  unfolding f₁-2morᵀ

  inv₂-ret-rhsᵀ : MorTm f₁-2morᵀ f₁-2morᵀ
  inv₂-ret-rhsᵀ = mor2-typed (id₂ f₁-2mor)

opaque
  unfolding inv₂-ret-ty

  inv₂-ret-lhs-typed : HasTy (TmTyped.tm inv₂-ret-lhsᵀ) inv₂-ret-ty
  inv₂-ret-lhs-typed =
    tyOf≡→HasTy (TmTyped.tp inv₂-ret-lhsᵀ)

opaque
  unfolding inv₂-ret-ty

  inv₂-ret-rhs-typed : HasTy (TmTyped.tm inv₂-ret-rhsᵀ) inv₂-ret-ty
  inv₂-ret-rhs-typed =
    tyOf≡→HasTy (TmTyped.tp inv₂-ret-rhsᵀ)

opaque
  unfolding f₁-2morᵀ inv₂-ret-ty inv₂-ret-lhsᵀ inv₂-ret-rhsᵀ

  inv₂-ret-full :
    FullMod.Full Γ-2mor-ps
      (Raw-Ty inv₂-ret-ty)
      (Raw-Tm (TmTyped.tm inv₂-ret-lhsᵀ))
      (Raw-Tm (TmTyped.tm inv₂-ret-rhsᵀ))
  inv₂-ret-full =
    FullMod.full-INVCOH-
      record
        { positive-dim = s≤s (s≤s z≤n)
        ; src-match = disc-src-bdry-match
        ; tgt-match = disc-src-bdry-match
        }

opaque
  inv₂-is-ret-tm :
    {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) → Tm Γ
  inv₂-is-ret-tm α =
    coh Γ-2mor-ps inv₂-ret-ty
      (TmTyped.tm inv₂-ret-lhsᵀ)
      (TmTyped.tm inv₂-ret-rhsᵀ)
      inv₂-ret-lhs-typed
      inv₂-ret-rhs-typed
      inv₂-ret-full
      (γ-2mor α)

opaque
  unfolding α-2morᵀ

  inv₂-ret-α-image :
    {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) →
    TmTyped.tm α-2morᵀ [ γ-2mor α ]t ≡ Mor₂.tm α
  inv₂-ret-α-image α = Tm-ext refl

opaque
  unfolding inv₂-α-2morᵀ inv₂

  inv₂-ret-inv-image :
    {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) →
    TmTyped.tm inv₂-α-2morᵀ [ γ-2mor α ]t ≡ Mor₂.tm (inv₂ α)
  inv₂-ret-inv-image α = Tm-ext refl

opaque
  unfolding inv₂-ret-rhsᵀ id₂ id₂-direct

  inv₂-ret-rhs-image :
    {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) →
    TmTyped.tm inv₂-ret-rhsᵀ [ γ-2mor α ]t ≡ Mor₂.tm (id₂ f)
  inv₂-ret-rhs-image α = Tm-ext refl

opaque
  unfolding inv₂-is-ret-tm inv₂-ret-ty inv₂-ret-lhsᵀ inv₂-ret-rhsᵀ _•₂_ comp₂-direct id₂ id₂-direct inv₂

  inv₂-is-ret-typed :
    {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} →
    (α : Mor₂ f g) →
    HasTy (inv₂-is-ret-tm α)
        (homTy ([⇒] f ⇒ f)
        (Mor₂.tm (inv₂ α •₂ α))
        (Mor₂.tm (id₂ f))
        (Mor₂.hasTy (inv₂ α •₂ α))
        (Mor₂.hasTy (id₂ f)))
  inv₂-is-ret-typed α = refl

opaque
  inv₂-is-ret : {Γ : Ctx} {x y : Obj Γ} {f g : Mor x y} → (α : Mor₂ f g)
    → Mor₃ ((inv₂ α) •₂ α) (id₂ f)
  inv₂-is-ret α = mkMor₃ (inv₂-is-ret-tm α) (inv₂-is-ret-typed α)
```
