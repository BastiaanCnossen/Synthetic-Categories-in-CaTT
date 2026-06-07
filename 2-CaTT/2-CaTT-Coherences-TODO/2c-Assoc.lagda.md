# 2c-Assoc: Associativity Coherences

```agda
module 2c-Assoc where

import 1a-RawSyntax-Comp as Raw
import 1b-Dependency-Comp as Dep
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
## Associativity

```agda
opaque
  unfolding _•₁_

  mor-typed-•₁ : {Γ : Ctx} {x y z : Obj Γ}
    → (f : Mor x y) → (g : Mor y z)
    → mor-typed (g •₁ f) ≡ mor-typed g • mor-typed f
  mor-typed-•₁ f g = TmTyped-ext refl

assoc-zps : (n : ℕ) → VarPs (Whisk.Γ-comp n) (Whisk.Γ-comp-ps n)
assoc-zps n = Whisk.W.varps-y (Whisk.comp-mid n)

assoc-z-tyᵀ : (n : ℕ) → Ty (Whisk.Γ-comp n)
assoc-z-tyᵀ n = varps-to-type {Γ = Whisk.Γ-comp n} (assoc-zps n)

Γ-assocᵀ : ℕ → Ctx
Γ-assocᵀ n = ext-ctx {Γ = Whisk.Γ-comp n} (assoc-zps n)

Γ-assocᵀ-ps : (n : ℕ) → Ps.CtxPs (Raw-Ctx (Γ-assocᵀ n))
Γ-assocᵀ-ps n = Ps.ps-ext (assoc-zps n)

assoc-baseᵀ : (n : ℕ) → Ty (Γ-assocᵀ n)
assoc-baseᵀ n = varps-to-type {Γ = Γ-assocᵀ n} (Whisk.W.varps-y (assoc-zps n))

assoc-Hᵀ : (n : ℕ) → Ty (Whisk.Γ-comp n ▸ assoc-z-tyᵀ n)
assoc-Hᵀ n =
  [ wkTy (assoc-z-tyᵀ n) ]
    vs (Whisk.W.varps-to-var (assoc-zps n))
    ⇒ vz :[ refl , refl ]

assoc-drop : (n : ℕ) → Sub (Γ-assocᵀ n) (Whisk.Γ-comp n)
assoc-drop n =
  wkSub {A = assoc-Hᵀ n}
    (wkSub {A = assoc-z-tyᵀ n} (idS (Whisk.Γ-comp n)))

raw-[]-wkSub²-id-T :
  {Γ : Raw.RawCtx}
  {E : Raw.RawTy Γ}
  {F : Raw.RawTy (Γ Raw.▸ E)}
  → (A : Raw.RawTy Γ)
  → A Raw.[ Raw.wkSub {A = F} (Raw.wkSub {A = E} (Raw.idS Γ)) ]T
    ≡ Raw.wkTy {A = F} (Raw.wkTy {A = E} A)
raw-[]-wkSub²-id-T {Γ = Γ} {E = E} {F = F} A =
  trans
    (sym
      (Raw.wkTy-[]T-r
        {B = F}
        A
        (Raw.wkSub {A = E} (Raw.idS Γ))))
    (trans
      (cong
        (Raw.wkTy {A = F})
        (sym
          (Raw.wkTy-[]T-r
            {B = E}
            A
            (Raw.idS Γ))))
      (cong
        (λ A₀ → Raw.wkTy {A = F} (Raw.wkTy {A = E} A₀))
        (Raw.[idS]T A)))

raw-[]-wkSub²-id-t :
  {Γ : Raw.RawCtx}
  {E : Raw.RawTy Γ}
  {F : Raw.RawTy (Γ Raw.▸ E)}
  → (t : Raw.RawTm Γ)
  → t Raw.[ Raw.wkSub {A = F} (Raw.wkSub {A = E} (Raw.idS Γ)) ]t
    ≡ Raw.wkTm {A = F} (Raw.wkTm {A = E} t)
raw-[]-wkSub²-id-t {Γ = Γ} {E = E} {F = F} t =
  trans
    (sym
      (Raw.wkTm-[]t-r
        {B = F}
        t
        (Raw.wkSub {A = E} (Raw.idS Γ))))
    (trans
      (cong
        (Raw.wkTm {A = F})
        (sym
          (Raw.wkTm-[]t-r
            {B = E}
            t
            (Raw.idS Γ))))
      (cong
        (λ t₀ → Raw.wkTm {A = F} (Raw.wkTm {A = E} t₀))
        (Raw.[idS]t t)))

assoc-y-varᶜ : (n : ℕ) → Var (Whisk.Γ-comp n)
assoc-y-varᶜ n = Raw.succ (Raw.succ (Whisk.W.varps-to-var (Whisk.comp-mid n)))

assoc-f-varᶜ : (n : ℕ) → Var (Whisk.Γ-comp n)
assoc-f-varᶜ n = Raw.succ (Raw.succ (Whisk.W.varps-to-var (Whisk.W.cell-dangling (suc n))))

assoc-xᵀ : (n : ℕ) → TmTyped (assoc-baseᵀ n)
assoc-xᵀ n = mk (var (Raw.succ (Raw.succ (Whisk.comp-src-var n)))) (Ty-ext refl)

assoc-yᵀ : (n : ℕ) → TmTyped (assoc-baseᵀ n)
assoc-yᵀ n = mk (var (Raw.succ (Raw.succ (assoc-y-varᶜ n)))) (Ty-ext refl)

assoc-zᵀ : (n : ℕ) → TmTyped (assoc-baseᵀ n)
assoc-zᵀ n = mk (var (Raw.succ (Raw.succ (Whisk.comp-tgt-var n)))) (Ty-ext refl)

assoc-wᵀ : (n : ℕ) → TmTyped (assoc-baseᵀ n)
assoc-wᵀ n = mk (var (Raw.succ Raw.zero)) (Ty-ext refl)

assoc-fᵀ : (n : ℕ) → MorTm (assoc-xᵀ n) (assoc-yᵀ n)
assoc-fᵀ n = mk (var (Raw.succ (Raw.succ (assoc-f-varᶜ n)))) (Ty-ext refl)

assoc-gᵀ : (n : ℕ) → MorTm (assoc-yᵀ n) (assoc-zᵀ n)
assoc-gᵀ n = mk (var (Raw.succ (Raw.succ Raw.zero))) (Ty-ext refl)

assoc-hᵀ : (n : ℕ) → MorTm (assoc-zᵀ n) (assoc-wᵀ n)
assoc-hᵀ n = mk (var Raw.zero) (Ty-ext refl)

abstract
  assoc-drop-comp-ty-image : (n : ℕ)
    → Whisk.W.Γ-comp-ty-raw n Raw.[ Raw-Sub (assoc-drop n) ]T
      ≡ Raw-Ty (assoc-baseᵀ n)
  assoc-drop-comp-ty-image n =
    trans
      (raw-[]-wkSub²-id-T (Whisk.W.Γ-comp-ty-raw n))
      (cong
        (λ A₀ → Raw.wkTy (Raw.wkTy A₀))
        (Whisk.W.Γ-comp-ty-raw-match n))

abstract
  assoc-drop-comp-src-image : (n : ℕ)
    → Whisk.W.Γ-comp-src-raw n Raw.[ Raw-Sub (assoc-drop n) ]t
      ≡ Raw-Tm (TmTyped.tm (assoc-xᵀ n))
  assoc-drop-comp-src-image n =
    trans
      (raw-[]-wkSub²-id-t (Whisk.W.Γ-comp-src-raw n))
      (cong
        (λ t → Raw.wkTm (Raw.wkTm t))
        (Whisk.W.Γ-comp-src-raw-match n))

abstract
  assoc-drop-comp-tgt-image : (n : ℕ)
    → Whisk.W.Γ-comp-tgt-raw n Raw.[ Raw-Sub (assoc-drop n) ]t
      ≡ Raw-Tm (TmTyped.tm (assoc-zᵀ n))
  assoc-drop-comp-tgt-image n =
    trans
      (raw-[]-wkSub²-id-t (Whisk.W.Γ-comp-tgt-raw n))
      (cong
        (λ t → Raw.wkTm (Raw.wkTm t))
        (Whisk.W.Γ-comp-tgt-raw-match n))

abstract
  assoc-gfᵀ-type-image : (n : ℕ)
    → Raw-Ty (Whisk.right-whisker-ty-univ n 0 [ assoc-drop n ]T)
      ≡ Raw-Ty (MorTy (assoc-xᵀ n) (assoc-zᵀ n))
  assoc-gfᵀ-type-image n =
    trans
      (cong
        (λ A₀ → A₀ Raw.[ Raw-Sub (assoc-drop n) ]T)
        (Whisk.right-whisker-ty-univ0-raw n))
      (trans
        (cong
          (λ A₀ → A₀ Raw.[ Raw-Sub (assoc-drop n) ]T)
          (Whisk.W.Γ-comp-univ-ty-raw-match n))
        (trans
          (cong
            (λ A₀ →
              Raw.[ A₀ ]
                (Whisk.W.Γ-comp-src-raw n Raw.[ Raw-Sub (assoc-drop n) ]t)
                ⇒
                (Whisk.W.Γ-comp-tgt-raw n Raw.[ Raw-Sub (assoc-drop n) ]t))
            (assoc-drop-comp-ty-image n))
          (trans
            (cong
              (λ s →
                Raw.[ Raw-Ty (assoc-baseᵀ n) ]
                  s
                  ⇒
                  (Whisk.W.Γ-comp-tgt-raw n Raw.[ Raw-Sub (assoc-drop n) ]t))
              (assoc-drop-comp-src-image n))
            (cong
              (λ t →
                Raw.[ Raw-Ty (assoc-baseᵀ n) ]
                  (Raw-Tm (TmTyped.tm (assoc-xᵀ n)))
                  ⇒ t)
              (assoc-drop-comp-tgt-image n)))))

assoc-gfᵀ-tm : (n : ℕ) → Tm (Γ-assocᵀ n)
assoc-gfᵀ-tm n = Whisk.right-whisker-tm-univ n 0 [ assoc-drop n ]t

abstract
  assoc-gfᵀ-typed : (n : ℕ)
    → tyOf (assoc-gfᵀ-tm n) ≡ MorTy (assoc-xᵀ n) (assoc-zᵀ n)
  assoc-gfᵀ-typed n =
    trans
      (tyOfSub
        {t = Whisk.right-whisker-tm-univ n 0}
        {A = Whisk.right-whisker-ty-univ n 0}
        {σ = assoc-drop n}
        (Whisk.right-whisker-tm-typed-univ n 0))
      (Ty-ext (assoc-gfᵀ-type-image n))

assoc-gfᵀ : (n : ℕ) → MorTm (assoc-xᵀ n) (assoc-zᵀ n)
assoc-gfᵀ n = mk (assoc-gfᵀ-tm n) (assoc-gfᵀ-typed n)

assoc-f-disk-raw :
  (n : ℕ)
  → Raw.RawSub (Raw-Ctx (Γ-assocᵀ n)) (Whisk.W.Γ-disk (suc n))
assoc-f-disk-raw n =
  Whisk.Γ-comp-disk-raw n Raw.∘ Raw-Sub (assoc-drop n)

assoc-g-src-disk-raw :
  (n : ℕ)
  → Raw.RawSub (Raw-Ctx (Γ-assocᵀ n)) (Whisk.W.Γ-disk n)
assoc-g-src-disk-raw n =
  Whisk.W.disk-prev-tgt-raw n Raw.∘ assoc-f-disk-raw n

assoc-g-disk-raw :
  (n : ℕ)
  → Raw.RawSub (Raw-Ctx (Γ-assocᵀ n)) (Whisk.W.Γ-disk (suc n))
assoc-g-disk-raw n =
  Raw.⟨
    Raw.⟨
      assoc-g-src-disk-raw n
    , Raw-Tm (TmTyped.tm (assoc-zᵀ n)) ⟩
  , Raw-Tm (TmTyped.tm (assoc-gᵀ n)) ⟩

assoc-gf-src-disk-raw :
  (n : ℕ)
  → Raw.RawSub (Raw-Ctx (Γ-assocᵀ n)) (Whisk.W.Γ-disk n)
assoc-gf-src-disk-raw n =
  Whisk.W.disk-prev-src-raw n Raw.∘ assoc-f-disk-raw n

assoc-gf-disk-raw :
  (n : ℕ)
  → Raw.RawSub (Raw-Ctx (Γ-assocᵀ n)) (Whisk.W.Γ-disk (suc n))
assoc-gf-disk-raw n =
  Raw.⟨
    Raw.⟨
      assoc-gf-src-disk-raw n
    , Raw-Tm (TmTyped.tm (assoc-zᵀ n)) ⟩
  , Raw-Tm (assoc-gfᵀ-tm n) ⟩

assoc-f-disk :
  (n : ℕ)
  → Sub (Γ-assocᵀ n) (Whisk.Γ-disk (suc n))
assoc-f-disk n =
  Whisk.Γ-comp-disk n ∘ assoc-drop n

assoc-gf-src-disk :
  (n : ℕ)
  → Sub (Γ-assocᵀ n) (Whisk.Γ-disk n)
assoc-gf-src-disk n =
  Whisk.disk-prev-src-sub n ∘ assoc-f-disk n

assoc-g-src-disk :
  (n : ℕ)
  → Sub (Γ-assocᵀ n) (Whisk.Γ-disk n)
assoc-g-src-disk n =
  Whisk.disk-prev-tgt-sub n ∘ assoc-f-disk n

abstract
  assoc-f-disk-endpoint-type-imageᵀ : (n : ℕ)
    → Whisk.W.disk-endpoint-ty n Raw.[ assoc-f-disk-raw n ]T
      ≡ Raw-Ty (assoc-baseᵀ n)
  assoc-f-disk-endpoint-type-imageᵀ n =
    trans
      (Raw.[∘]T
        (Whisk.W.disk-endpoint-ty n)
        (Whisk.Γ-comp-disk-raw n)
        (Raw-Sub (assoc-drop n)))
      (trans
        (cong
          (λ A₀ → A₀ Raw.[ Raw-Sub (assoc-drop n) ]T)
          (Whisk.Γ-comp-disk-endpoint-type-image n))
        (assoc-drop-comp-ty-image n))

abstract
  assoc-f-disk-tgt-imageᵀ : (n : ℕ)
    → Whisk.W.disk-tgt n Raw.[ assoc-f-disk-raw n ]t
      ≡ Raw-Tm (TmTyped.tm (assoc-yᵀ n))
  assoc-f-disk-tgt-imageᵀ n =
    trans
      (Raw.[∘]t
        (Whisk.W.disk-tgt n)
        (Whisk.Γ-comp-disk-raw n)
        (Raw-Sub (assoc-drop n)))
      (trans
        (cong
          (λ t → t Raw.[ Raw-Sub (assoc-drop n) ]t)
          (raw-[]-wkSub²-id-t
            {E = Whisk.W.varps-to-type (Whisk.comp-mid n)}
            {F = Whisk.W.hom-type-ext (Whisk.comp-mid n)}
            (Whisk.W.disk-tgt n)))
        (raw-[]-wkSub²-id-t
          (Raw.wkTm (Raw.wkTm (Whisk.W.disk-tgt n)))))

abstract
  assoc-f-disk-src-imageᵀ : (n : ℕ)
    → Whisk.W.disk-src n Raw.[ assoc-f-disk-raw n ]t
      ≡ Raw-Tm (TmTyped.tm (assoc-xᵀ n))
  assoc-f-disk-src-imageᵀ n =
    trans
      (Raw.[∘]t
        (Whisk.W.disk-src n)
        (Whisk.Γ-comp-disk-raw n)
        (Raw-Sub (assoc-drop n)))
      (trans
        (cong
          (λ t → t Raw.[ Raw-Sub (assoc-drop n) ]t)
          (raw-[]-wkSub²-id-t
            {E = Whisk.W.varps-to-type (Whisk.comp-mid n)}
            {F = Whisk.W.hom-type-ext (Whisk.comp-mid n)}
            (Whisk.W.disk-src n)))
        (raw-[]-wkSub²-id-t
          (Raw.wkTm (Raw.wkTm (Whisk.W.disk-src n)))))

abstract
  assoc-f-disk-mid-type-imageᵀ : (n : ℕ)
    → Whisk.W.varps-to-type (Whisk.comp-mid n) Raw.[ assoc-f-disk-raw n ]T
      ≡ Raw-Ty (assoc-baseᵀ n)
  assoc-f-disk-mid-type-imageᵀ n =
    assoc-f-disk-endpoint-type-imageᵀ n

abstract
  assoc-gf-src-disk-base-imageᵀ : (n : ℕ)
    → Whisk.W.A-disk n Raw.[ assoc-gf-src-disk-raw n ]T
      ≡ Raw-Ty (assoc-baseᵀ n)
  assoc-gf-src-disk-base-imageᵀ n =
    trans
      (Raw.[∘]T
        (Whisk.W.A-disk n)
        (Whisk.W.disk-prev-src-raw n)
        (assoc-f-disk-raw n))
      (trans
        (cong
          (λ A₀ → A₀ Raw.[ assoc-f-disk-raw n ]T)
          (Whisk.disk-prev-src-A-disk-image n))
        (assoc-f-disk-endpoint-type-imageᵀ n))

abstract
  assoc-gf-src-disk-cell-imageᵀ : (n : ℕ)
    → Whisk.W.cell n Raw.[ assoc-gf-src-disk-raw n ]t
      ≡ Raw-Tm (TmTyped.tm (assoc-xᵀ n))
  assoc-gf-src-disk-cell-imageᵀ n =
    trans
      (Raw.[∘]t
        (Whisk.W.cell n)
        (Whisk.W.disk-prev-src-raw n)
        (assoc-f-disk-raw n))
      (trans
        (cong
          (λ t → t Raw.[ assoc-f-disk-raw n ]t)
          (raw-γ-disk-cast-cell-image
            {A = Whisk.W.disk-endpoint-ty n}
            {a = Whisk.W.disk-src n}
            n
            (Whisk.W.dim-disk-endpoint-ty n)
            (Whisk.W.disk-endpoint-diskTy n)
            refl))
        (assoc-f-disk-src-imageᵀ n))

abstract
  assoc-gf-disk-top-type-imageᵀ : (n : ℕ)
    → Whisk.W.hom-type-ext (Whisk.W.cell-dangling n)
        Raw.[
          Raw.⟨
            assoc-gf-src-disk-raw n
          , Raw-Tm (TmTyped.tm (assoc-zᵀ n)) ⟩
        ]T
      ≡ Raw-Ty (MorTy (assoc-xᵀ n) (assoc-zᵀ n))
  assoc-gf-disk-top-type-imageᵀ n =
    trans
      (cong
        (λ A₀ →
          Raw.[ A₀ ]
            (Raw.wkTm {A = Whisk.W.A-disk n} (Whisk.W.cell n)
              Raw.[
                Raw.⟨
                  assoc-gf-src-disk-raw n
                , Raw-Tm (TmTyped.tm (assoc-zᵀ n)) ⟩
              ]t)
            ⇒ Raw-Tm (TmTyped.tm (assoc-zᵀ n)))
        (Raw.wkTy-[]T
          (Whisk.W.A-disk n)
          (assoc-gf-src-disk-raw n)
          (Raw-Tm (TmTyped.tm (assoc-zᵀ n)))))
      (trans
        (cong
          (λ s →
            Raw.[ Whisk.W.A-disk n Raw.[ assoc-gf-src-disk-raw n ]T ]
              s
              ⇒ Raw-Tm (TmTyped.tm (assoc-zᵀ n)))
          (Raw.wkTm-[]t
            {A = Whisk.W.A-disk n}
            (Whisk.W.cell n)
            (assoc-gf-src-disk-raw n)
            (Raw-Tm (TmTyped.tm (assoc-zᵀ n)))))
        (trans
          (cong
            (λ A₀ →
              Raw.[ A₀ ]
                (Whisk.W.cell n Raw.[ assoc-gf-src-disk-raw n ]t)
                ⇒ Raw-Tm (TmTyped.tm (assoc-zᵀ n)))
            (assoc-gf-src-disk-base-imageᵀ n))
          (cong
            (λ s →
              Raw.[ Raw-Ty (assoc-baseᵀ n) ]
                s
                ⇒ Raw-Tm (TmTyped.tm (assoc-zᵀ n)))
            (assoc-gf-src-disk-cell-imageᵀ n))))

abstract
  assoc-g-src-disk-base-imageᵀ : (n : ℕ)
    → Whisk.W.A-disk n Raw.[ assoc-g-src-disk-raw n ]T
      ≡ Raw-Ty (assoc-baseᵀ n)
  assoc-g-src-disk-base-imageᵀ n =
    trans
      (Raw.[∘]T
        (Whisk.W.A-disk n)
        (Whisk.W.disk-prev-tgt-raw n)
        (assoc-f-disk-raw n))
      (trans
        (cong
          (λ A₀ → A₀ Raw.[ assoc-f-disk-raw n ]T)
          (Whisk.disk-prev-tgt-A-disk-image n))
        (assoc-f-disk-endpoint-type-imageᵀ n))

abstract
  assoc-g-src-disk-cell-imageᵀ : (n : ℕ)
    → Whisk.W.cell n Raw.[ assoc-g-src-disk-raw n ]t
      ≡ Raw-Tm (TmTyped.tm (assoc-yᵀ n))
  assoc-g-src-disk-cell-imageᵀ n =
    trans
      (Raw.[∘]t
        (Whisk.W.cell n)
        (Whisk.W.disk-prev-tgt-raw n)
        (assoc-f-disk-raw n))
      (trans
        (cong
          (λ t → t Raw.[ assoc-f-disk-raw n ]t)
          (raw-γ-disk-cast-cell-image
            {A = Whisk.W.disk-endpoint-ty n}
            {a = Whisk.W.disk-tgt n}
            n
            (Whisk.W.dim-disk-endpoint-ty n)
            (Whisk.W.disk-endpoint-diskTy n)
            refl))
        (assoc-f-disk-tgt-imageᵀ n))

abstract
  assoc-g-disk-top-type-imageᵀ : (n : ℕ)
    → Whisk.W.hom-type-ext (Whisk.W.cell-dangling n)
        Raw.[
          Raw.⟨
            assoc-g-src-disk-raw n
          , Raw-Tm (TmTyped.tm (assoc-zᵀ n)) ⟩
        ]T
      ≡ Raw-Ty (MorTy (assoc-yᵀ n) (assoc-zᵀ n))
  assoc-g-disk-top-type-imageᵀ n =
    trans
      (cong
        (λ A₀ →
          Raw.[ A₀ ]
            (Raw.wkTm {A = Whisk.W.A-disk n} (Whisk.W.cell n)
              Raw.[
                Raw.⟨
                  assoc-g-src-disk-raw n
                , Raw-Tm (TmTyped.tm (assoc-zᵀ n)) ⟩
              ]t)
            ⇒ Raw-Tm (TmTyped.tm (assoc-zᵀ n)))
        (Raw.wkTy-[]T
          (Whisk.W.A-disk n)
          (assoc-g-src-disk-raw n)
          (Raw-Tm (TmTyped.tm (assoc-zᵀ n)))))
      (trans
        (cong
          (λ s →
            Raw.[ Whisk.W.A-disk n Raw.[ assoc-g-src-disk-raw n ]T ]
              s
              ⇒ Raw-Tm (TmTyped.tm (assoc-zᵀ n)))
          (Raw.wkTm-[]t
            {A = Whisk.W.A-disk n}
            (Whisk.W.cell n)
            (assoc-g-src-disk-raw n)
            (Raw-Tm (TmTyped.tm (assoc-zᵀ n)))))
        (trans
          (cong
            (λ A₀ →
              Raw.[ A₀ ]
                (Whisk.W.cell n Raw.[ assoc-g-src-disk-raw n ]t)
                ⇒ Raw-Tm (TmTyped.tm (assoc-zᵀ n)))
            (assoc-g-src-disk-base-imageᵀ n))
          (cong
            (λ s →
              Raw.[ Raw-Ty (assoc-baseᵀ n) ]
                s
                ⇒ Raw-Tm (TmTyped.tm (assoc-zᵀ n)))
            (assoc-g-src-disk-cell-imageᵀ n))))

assoc-z-disk-typed : (n : ℕ)
  → tyOf (TmTyped.tm (assoc-zᵀ n))
    ≡ Whisk.A-disk n [ assoc-g-src-disk n ]T
assoc-z-disk-typed n =
  trans
    (TmTyped.tp (assoc-zᵀ n))
    (sym (Ty-ext (assoc-g-src-disk-base-imageᵀ n)))

assoc-g-disk-step :
  (n : ℕ)
  → Sub
      (Γ-assocᵀ n)
      (Whisk.Γ-disk n ▸ Whisk.A-disk n)
assoc-g-disk-step n =
  ⟨ assoc-g-src-disk n , TmTyped.tm (assoc-zᵀ n) ⟩:[ assoc-z-disk-typed n ]

assoc-disk-top-ty :
  (n : ℕ)
  → Ty (Whisk.Γ-disk n ▸ Whisk.A-disk n)
assoc-disk-top-ty n =
  [ wkTy (Whisk.A-disk n) ]
    vs (Whisk.W.varps-to-var (Whisk.W.cell-dangling n))
    ⇒ vz :[ refl , refl ]

assoc-z-gf-disk-typed : (n : ℕ)
  → tyOf (TmTyped.tm (assoc-zᵀ n))
    ≡ Whisk.A-disk n [ assoc-gf-src-disk n ]T
assoc-z-gf-disk-typed n =
  trans
    (TmTyped.tp (assoc-zᵀ n))
    (sym (Ty-ext (assoc-gf-src-disk-base-imageᵀ n)))

assoc-gf-disk-step :
  (n : ℕ)
  → Sub
      (Γ-assocᵀ n)
      (Whisk.Γ-disk n ▸ Whisk.A-disk n)
assoc-gf-disk-step n =
  ⟨ assoc-gf-src-disk n , TmTyped.tm (assoc-zᵀ n) ⟩:[ assoc-z-gf-disk-typed n ]

assoc-gf-disk-top-typed : (n : ℕ)
  → tyOf (assoc-gfᵀ-tm n)
    ≡ assoc-disk-top-ty n [ assoc-gf-disk-step n ]T
assoc-gf-disk-top-typed n =
  trans
    (assoc-gfᵀ-typed n)
    (sym (Ty-ext (assoc-gf-disk-top-type-imageᵀ n)))

assoc-gf-disk-built :
  (n : ℕ)
  → Sub
      (Γ-assocᵀ n)
      ((Whisk.Γ-disk n ▸ Whisk.A-disk n) ▸ assoc-disk-top-ty n)
assoc-gf-disk-built n =
  ⟨ assoc-gf-disk-step n , assoc-gfᵀ-tm n ⟩:[ assoc-gf-disk-top-typed n ]

assoc-gf-disk :
  (n : ℕ)
  → Sub (Γ-assocᵀ n) (Whisk.Γ-disk (suc n))
assoc-gf-disk n =
  mkSub (assoc-gf-disk-raw n) (Sub-wf (assoc-gf-disk-built n))

abstract
  assoc-gf-disk-mid-type-imageᵀ : (n : ℕ)
    → Whisk.W.varps-to-type (Whisk.comp-mid n) Raw.[ assoc-gf-disk-raw n ]T
      ≡ Raw-Ty (assoc-baseᵀ n)
  assoc-gf-disk-mid-type-imageᵀ n =
    trans
      (Raw.wkTy-[]T
        (Raw.wkTy (Whisk.W.A-disk n))
        (Raw.⟨
          assoc-gf-src-disk-raw n
        , Raw-Tm (TmTyped.tm (assoc-zᵀ n)) ⟩)
        (Raw-Tm (assoc-gfᵀ-tm n)))
      (trans
        (Raw.wkTy-[]T
          (Whisk.W.A-disk n)
          (assoc-gf-src-disk-raw n)
          (Raw-Tm (TmTyped.tm (assoc-zᵀ n))))
        (assoc-gf-src-disk-base-imageᵀ n))

abstract
  assoc-gf-disk-mid-imageᵀ : (n : ℕ)
    → Raw.lookup (Whisk.W.varps-to-var (Whisk.comp-mid n)) (assoc-gf-disk-raw n)
      ≡ Raw-Tm (TmTyped.tm (assoc-zᵀ n))
  assoc-gf-disk-mid-imageᵀ n = refl

assoc-g-disk-top-typed : (n : ℕ)
  → tyOf (TmTyped.tm (assoc-gᵀ n))
    ≡ assoc-disk-top-ty n [ assoc-g-disk-step n ]T
assoc-g-disk-top-typed n =
  trans
    (TmTyped.tp (assoc-gᵀ n))
    (sym (Ty-ext (assoc-g-disk-top-type-imageᵀ n)))

assoc-g-disk-built :
  (n : ℕ)
  → Sub
      (Γ-assocᵀ n)
      ((Whisk.Γ-disk n ▸ Whisk.A-disk n) ▸ assoc-disk-top-ty n)
assoc-g-disk-built n =
  ⟨ assoc-g-disk-step n , TmTyped.tm (assoc-gᵀ n) ⟩:[ assoc-g-disk-top-typed n ]

assoc-g-disk :
  (n : ℕ)
  → Sub (Γ-assocᵀ n) (Whisk.Γ-disk (suc n))
assoc-g-disk n =
  mkSub (assoc-g-disk-raw n) (Sub-wf (assoc-g-disk-built n))

abstract
  assoc-g-disk-mid-type-imageᵀ : (n : ℕ)
    → Whisk.W.varps-to-type (Whisk.comp-mid n) Raw.[ assoc-g-disk-raw n ]T
      ≡ Raw-Ty (assoc-baseᵀ n)
  assoc-g-disk-mid-type-imageᵀ n =
    trans
      (Raw.wkTy-[]T
        (Raw.wkTy (Whisk.W.A-disk n))
        (Raw.⟨
          assoc-g-src-disk-raw n
        , Raw-Tm (TmTyped.tm (assoc-zᵀ n)) ⟩)
        (Raw-Tm (TmTyped.tm (assoc-gᵀ n))))
      (trans
        (Raw.wkTy-[]T
          (Whisk.W.A-disk n)
          (assoc-g-src-disk-raw n)
          (Raw-Tm (TmTyped.tm (assoc-zᵀ n))))
        (assoc-g-src-disk-base-imageᵀ n))

abstract
  assoc-g-disk-mid-imageᵀ : (n : ℕ)
    → Raw.lookup (Whisk.W.varps-to-var (Whisk.comp-mid n)) (assoc-g-disk-raw n)
      ≡ Raw-Tm (TmTyped.tm (assoc-zᵀ n))
  assoc-g-disk-mid-imageᵀ n = refl

assoc-hg-drop-raw :
  (n : ℕ)
  → Raw.RawSub (Raw-Ctx (Γ-assocᵀ n)) (Whisk.W.Γ-comp n)
assoc-hg-drop-raw n =
  Raw.⟨
    Raw.⟨
      assoc-g-disk-raw n
    , Raw-Tm (TmTyped.tm (assoc-wᵀ n)) ⟩
  , Raw-Tm (TmTyped.tm (assoc-hᵀ n)) ⟩

assoc-hg-w-typed : (n : ℕ)
  → tyOf (TmTyped.tm (assoc-wᵀ n))
    ≡ varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n) [ assoc-g-disk n ]T
assoc-hg-w-typed n =
  trans
    (TmTyped.tp (assoc-wᵀ n))
    (sym (Ty-ext (assoc-g-disk-mid-type-imageᵀ n)))

assoc-hg-drop-step :
  (n : ℕ)
  → Sub (Γ-assocᵀ n) (Whisk.Γ-disk (suc n) ▸ varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n))
assoc-hg-drop-step n =
  ⟨ assoc-g-disk n , TmTyped.tm (assoc-wᵀ n) ⟩:[ assoc-hg-w-typed n ]

abstract
  assoc-hg-drop-top-type-imageᵀ : (n : ℕ)
    → Whisk.W.hom-type-ext (Whisk.comp-mid n)
        Raw.[
          Raw.⟨
            assoc-g-disk-raw n
          , Raw-Tm (TmTyped.tm (assoc-wᵀ n)) ⟩
        ]T
      ≡ Raw-Ty (MorTy (assoc-zᵀ n) (assoc-wᵀ n))
  assoc-hg-drop-top-type-imageᵀ n =
    trans
      (cong
        (λ A₀ →
          Raw.[ A₀ ]
            (Raw.wkTm
              {A = Whisk.W.varps-to-type (Whisk.comp-mid n)}
              (Raw.var (Whisk.W.varps-to-var (Whisk.comp-mid n)))
              Raw.[
                Raw.⟨
                  assoc-g-disk-raw n
                , Raw-Tm (TmTyped.tm (assoc-wᵀ n)) ⟩
              ]t)
            ⇒ Raw-Tm (TmTyped.tm (assoc-wᵀ n)))
        (Raw.wkTy-[]T
          (Whisk.W.varps-to-type (Whisk.comp-mid n))
          (assoc-g-disk-raw n)
          (Raw-Tm (TmTyped.tm (assoc-wᵀ n)))))
      (trans
        (cong
          (λ s →
            Raw.[
              Whisk.W.varps-to-type (Whisk.comp-mid n)
                Raw.[ assoc-g-disk-raw n ]T
            ]
              s
              ⇒ Raw-Tm (TmTyped.tm (assoc-wᵀ n)))
          (Raw.wkTm-[]t
            {A = Whisk.W.varps-to-type (Whisk.comp-mid n)}
            (Raw.var (Whisk.W.varps-to-var (Whisk.comp-mid n)))
            (assoc-g-disk-raw n)
            (Raw-Tm (TmTyped.tm (assoc-wᵀ n)))))
        (trans
          (cong
            (λ A₀ →
              Raw.[ A₀ ]
                (Raw.lookup (Whisk.W.varps-to-var (Whisk.comp-mid n)) (assoc-g-disk-raw n))
                ⇒ Raw-Tm (TmTyped.tm (assoc-wᵀ n)))
            (assoc-g-disk-mid-type-imageᵀ n))
          (cong
            (λ s →
              Raw.[ Raw-Ty (assoc-baseᵀ n) ]
                s
                ⇒ Raw-Tm (TmTyped.tm (assoc-wᵀ n)))
            (assoc-g-disk-mid-imageᵀ n))))

assoc-hg-drop-top-typed : (n : ℕ)
  → tyOf (TmTyped.tm (assoc-hᵀ n))
    ≡
      [ wkTy (varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n)) ]
        vs (Whisk.W.varps-to-var (Whisk.comp-mid n))
        ⇒ vz :[ refl , refl ]
      [ assoc-hg-drop-step n ]T
assoc-hg-drop-top-typed n =
  trans
    (TmTyped.tp (assoc-hᵀ n))
    (sym (Ty-ext (assoc-hg-drop-top-type-imageᵀ n)))

assoc-hg-drop-built :
  (n : ℕ)
  → Sub
      (Γ-assocᵀ n)
      ((Whisk.Γ-disk (suc n) ▸ varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n))
        ▸
        [ wkTy (varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n)) ]
          vs (Whisk.W.varps-to-var (Whisk.comp-mid n))
          ⇒ vz :[ refl , refl ])
assoc-hg-drop-built n =
  ⟨ assoc-hg-drop-step n , TmTyped.tm (assoc-hᵀ n) ⟩:[ assoc-hg-drop-top-typed n ]

assoc-hg-drop :
  (n : ℕ)
  → Sub (Γ-assocᵀ n) (Whisk.Γ-comp n)
assoc-hg-drop n =
  mkSub (assoc-hg-drop-raw n) (Sub-wf (assoc-hg-drop-built n))

abstract
  assoc-hg-drop-comp-ty-image : (n : ℕ)
    → Whisk.W.Γ-comp-ty-raw n Raw.[ assoc-hg-drop-raw n ]T
      ≡ Raw-Ty (assoc-baseᵀ n)
  assoc-hg-drop-comp-ty-image n =
    trans
      (cong
        (λ A₀ → A₀ Raw.[ assoc-hg-drop-raw n ]T)
        (Whisk.W.Γ-comp-ty-raw-match n))
      (trans
        (Raw.wkTy-[]T
          (Raw.wkTy (Whisk.W.varps-to-type (Whisk.comp-mid n)))
          (Raw.⟨
            assoc-g-disk-raw n
          , Raw-Tm (TmTyped.tm (assoc-wᵀ n)) ⟩)
          (Raw-Tm (TmTyped.tm (assoc-hᵀ n))))
        (trans
          (Raw.wkTy-[]T
            (Whisk.W.varps-to-type (Whisk.comp-mid n))
            (assoc-g-disk-raw n)
            (Raw-Tm (TmTyped.tm (assoc-wᵀ n))))
          (assoc-g-disk-mid-type-imageᵀ n)))

abstract
  assoc-hg-drop-comp-src-image : (n : ℕ)
    → Whisk.W.Γ-comp-src-raw n Raw.[ assoc-hg-drop-raw n ]t
      ≡ Raw-Tm (TmTyped.tm (assoc-yᵀ n))
  assoc-hg-drop-comp-src-image n =
    trans
      (cong
        (λ t → t Raw.[ assoc-hg-drop-raw n ]t)
        (Whisk.W.Γ-comp-src-raw-match n))
      (assoc-g-src-disk-cell-imageᵀ n)

abstract
  assoc-hg-drop-comp-tgt-image : (n : ℕ)
    → Whisk.W.Γ-comp-tgt-raw n Raw.[ assoc-hg-drop-raw n ]t
      ≡ Raw-Tm (TmTyped.tm (assoc-wᵀ n))
  assoc-hg-drop-comp-tgt-image n =
    trans
      (cong
        (λ t → t Raw.[ assoc-hg-drop-raw n ]t)
        (Whisk.W.Γ-comp-tgt-raw-match n))
      refl

abstract
  assoc-hgᵀ-type-image : (n : ℕ)
    → Raw-Ty (Whisk.right-whisker-ty-univ n 0 [ assoc-hg-drop n ]T)
      ≡ Raw-Ty (MorTy (assoc-yᵀ n) (assoc-wᵀ n))
  assoc-hgᵀ-type-image n =
    trans
      (cong
        (λ A₀ → A₀ Raw.[ Raw-Sub (assoc-hg-drop n) ]T)
        (Whisk.right-whisker-ty-univ0-raw n))
      (trans
        (cong
          (λ A₀ → A₀ Raw.[ Raw-Sub (assoc-hg-drop n) ]T)
          (Whisk.W.Γ-comp-univ-ty-raw-match n))
        (trans
          (cong
            (λ A₀ →
              Raw.[ A₀ ]
                (Whisk.W.Γ-comp-src-raw n Raw.[ Raw-Sub (assoc-hg-drop n) ]t)
                ⇒
                (Whisk.W.Γ-comp-tgt-raw n Raw.[ Raw-Sub (assoc-hg-drop n) ]t))
            (assoc-hg-drop-comp-ty-image n))
          (trans
            (cong
              (λ s →
                Raw.[ Raw-Ty (assoc-baseᵀ n) ]
                  s
                  ⇒
                  (Whisk.W.Γ-comp-tgt-raw n Raw.[ Raw-Sub (assoc-hg-drop n) ]t))
              (assoc-hg-drop-comp-src-image n))
            (cong
              (λ t →
                Raw.[ Raw-Ty (assoc-baseᵀ n) ]
                  (Raw-Tm (TmTyped.tm (assoc-yᵀ n)))
                  ⇒ t)
              (assoc-hg-drop-comp-tgt-image n)))))

assoc-hgᵀ-tm : (n : ℕ) → Tm (Γ-assocᵀ n)
assoc-hgᵀ-tm n =
  Whisk.right-whisker-tm-univ n 0 [ assoc-hg-drop n ]t

abstract
  assoc-hgᵀ-typed : (n : ℕ)
    → tyOf (assoc-hgᵀ-tm n) ≡ MorTy (assoc-yᵀ n) (assoc-wᵀ n)
  assoc-hgᵀ-typed n =
    trans
      (tyOfSub
        {t = Whisk.right-whisker-tm-univ n 0}
        {A = Whisk.right-whisker-ty-univ n 0}
        {σ = assoc-hg-drop n}
        (Whisk.right-whisker-tm-typed-univ n 0))
      (Ty-ext (assoc-hgᵀ-type-image n))

assoc-hgᵀ : (n : ℕ) → MorTm (assoc-yᵀ n) (assoc-wᵀ n)
assoc-hgᵀ n = mk (assoc-hgᵀ-tm n) (assoc-hgᵀ-typed n)

assoc-tgt-drop-raw :
  (n : ℕ)
  → Raw.RawSub (Raw-Ctx (Γ-assocᵀ n)) (Whisk.W.Γ-comp n)
assoc-tgt-drop-raw n =
  Raw.⟨
    Raw.⟨
      assoc-f-disk-raw n
    , Raw-Tm (TmTyped.tm (assoc-wᵀ n)) ⟩
  , Raw-Tm (assoc-hgᵀ-tm n) ⟩

assoc-tgt-w-typed : (n : ℕ)
  → tyOf (TmTyped.tm (assoc-wᵀ n))
    ≡ varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n) [ assoc-f-disk n ]T
assoc-tgt-w-typed n =
  trans
    (TmTyped.tp (assoc-wᵀ n))
    (sym (Ty-ext (assoc-f-disk-mid-type-imageᵀ n)))

assoc-tgt-drop-step :
  (n : ℕ)
  → Sub (Γ-assocᵀ n) (Whisk.Γ-disk (suc n) ▸ varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n))
assoc-tgt-drop-step n =
  ⟨ assoc-f-disk n , TmTyped.tm (assoc-wᵀ n) ⟩:[ assoc-tgt-w-typed n ]

abstract
  assoc-tgt-drop-top-type-imageᵀ : (n : ℕ)
    → Whisk.W.hom-type-ext (Whisk.comp-mid n)
        Raw.[
          Raw.⟨
            assoc-f-disk-raw n
          , Raw-Tm (TmTyped.tm (assoc-wᵀ n)) ⟩
        ]T
      ≡ Raw-Ty (MorTy (assoc-yᵀ n) (assoc-wᵀ n))
  assoc-tgt-drop-top-type-imageᵀ n =
    trans
      (cong
        (λ A₀ →
          Raw.[ A₀ ]
            (Raw.wkTm
              {A = Whisk.W.varps-to-type (Whisk.comp-mid n)}
              (Raw.var (Whisk.W.varps-to-var (Whisk.comp-mid n)))
              Raw.[
                Raw.⟨
                  assoc-f-disk-raw n
                , Raw-Tm (TmTyped.tm (assoc-wᵀ n)) ⟩
              ]t)
            ⇒ Raw-Tm (TmTyped.tm (assoc-wᵀ n)))
        (Raw.wkTy-[]T
          (Whisk.W.varps-to-type (Whisk.comp-mid n))
          (assoc-f-disk-raw n)
          (Raw-Tm (TmTyped.tm (assoc-wᵀ n)))))
      (trans
        (cong
          (λ s →
            Raw.[
              Whisk.W.varps-to-type (Whisk.comp-mid n)
                Raw.[ assoc-f-disk-raw n ]T
            ]
              s
              ⇒ Raw-Tm (TmTyped.tm (assoc-wᵀ n)))
          (Raw.wkTm-[]t
            {A = Whisk.W.varps-to-type (Whisk.comp-mid n)}
            (Raw.var (Whisk.W.varps-to-var (Whisk.comp-mid n)))
            (assoc-f-disk-raw n)
            (Raw-Tm (TmTyped.tm (assoc-wᵀ n)))))
        (trans
          (cong
            (λ A₀ →
              Raw.[ A₀ ]
                (Raw.lookup (Whisk.W.varps-to-var (Whisk.comp-mid n)) (assoc-f-disk-raw n))
                ⇒ Raw-Tm (TmTyped.tm (assoc-wᵀ n)))
            (assoc-f-disk-mid-type-imageᵀ n))
          (cong
            (λ s →
              Raw.[ Raw-Ty (assoc-baseᵀ n) ]
                s
                ⇒ Raw-Tm (TmTyped.tm (assoc-wᵀ n)))
            (assoc-f-disk-tgt-imageᵀ n))))

assoc-tgt-drop-top-typed : (n : ℕ)
  → tyOf (assoc-hgᵀ-tm n)
    ≡
      [ wkTy (varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n)) ]
        vs (Whisk.W.varps-to-var (Whisk.comp-mid n))
        ⇒ vz :[ refl , refl ]
      [ assoc-tgt-drop-step n ]T
assoc-tgt-drop-top-typed n =
  trans
    (assoc-hgᵀ-typed n)
    (sym (Ty-ext (assoc-tgt-drop-top-type-imageᵀ n)))

assoc-tgt-drop-built :
  (n : ℕ)
  → Sub
      (Γ-assocᵀ n)
      ((Whisk.Γ-disk (suc n) ▸ varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n))
        ▸
        [ wkTy (varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n)) ]
          vs (Whisk.W.varps-to-var (Whisk.comp-mid n))
          ⇒ vz :[ refl , refl ])
assoc-tgt-drop-built n =
  ⟨ assoc-tgt-drop-step n , assoc-hgᵀ-tm n ⟩:[ assoc-tgt-drop-top-typed n ]

assoc-tgt-drop :
  (n : ℕ)
  → Sub (Γ-assocᵀ n) (Whisk.Γ-comp n)
assoc-tgt-drop n =
  mkSub (assoc-tgt-drop-raw n) (Sub-wf (assoc-tgt-drop-built n))

abstract
  assoc-tgt-drop-comp-ty-image : (n : ℕ)
    → Whisk.W.Γ-comp-ty-raw n Raw.[ assoc-tgt-drop-raw n ]T
      ≡ Raw-Ty (assoc-baseᵀ n)
  assoc-tgt-drop-comp-ty-image n =
    trans
      (cong
        (λ A₀ → A₀ Raw.[ assoc-tgt-drop-raw n ]T)
        (Whisk.W.Γ-comp-ty-raw-match n))
      (trans
        (Raw.wkTy-[]T
          (Raw.wkTy (Whisk.W.varps-to-type (Whisk.comp-mid n)))
          (Raw.⟨
            assoc-f-disk-raw n
          , Raw-Tm (TmTyped.tm (assoc-wᵀ n)) ⟩)
          (Raw-Tm (assoc-hgᵀ-tm n)))
        (trans
          (Raw.wkTy-[]T
          (Whisk.W.varps-to-type (Whisk.comp-mid n))
          (assoc-f-disk-raw n)
          (Raw-Tm (TmTyped.tm (assoc-wᵀ n))))
        (assoc-f-disk-mid-type-imageᵀ n)))

abstract
  assoc-tgt-drop-comp-src-image : (n : ℕ)
    → Whisk.W.Γ-comp-src-raw n Raw.[ assoc-tgt-drop-raw n ]t
      ≡ Raw-Tm (TmTyped.tm (assoc-xᵀ n))
  assoc-tgt-drop-comp-src-image n =
    trans
      (cong
        (λ t → t Raw.[ assoc-tgt-drop-raw n ]t)
        (Whisk.W.Γ-comp-src-raw-match n))
      (assoc-f-disk-src-imageᵀ n)

abstract
  assoc-tgt-drop-comp-tgt-image : (n : ℕ)
    → Whisk.W.Γ-comp-tgt-raw n Raw.[ assoc-tgt-drop-raw n ]t
      ≡ Raw-Tm (TmTyped.tm (assoc-wᵀ n))
  assoc-tgt-drop-comp-tgt-image n =
    trans
      (cong
        (λ t → t Raw.[ assoc-tgt-drop-raw n ]t)
        (Whisk.W.Γ-comp-tgt-raw-match n))
      refl

assoc-src-drop-raw :
  (n : ℕ)
  → Raw.RawSub (Raw-Ctx (Γ-assocᵀ n)) (Whisk.W.Γ-comp n)
assoc-src-drop-raw n =
  Raw.⟨
    Raw.⟨
      assoc-gf-disk-raw n
    , Raw-Tm (TmTyped.tm (assoc-wᵀ n)) ⟩
  , Raw-Tm (TmTyped.tm (assoc-hᵀ n)) ⟩

assoc-src-w-typed : (n : ℕ)
  → tyOf (TmTyped.tm (assoc-wᵀ n))
    ≡ varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n) [ assoc-gf-disk n ]T
assoc-src-w-typed n =
  trans
    (TmTyped.tp (assoc-wᵀ n))
    (sym (Ty-ext (assoc-gf-disk-mid-type-imageᵀ n)))

assoc-src-drop-step :
  (n : ℕ)
  → Sub (Γ-assocᵀ n) (Whisk.Γ-disk (suc n) ▸ varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n))
assoc-src-drop-step n =
  ⟨ assoc-gf-disk n , TmTyped.tm (assoc-wᵀ n) ⟩:[ assoc-src-w-typed n ]

abstract
  assoc-src-drop-top-type-imageᵀ : (n : ℕ)
    → Whisk.W.hom-type-ext (Whisk.comp-mid n)
        Raw.[
          Raw.⟨
            assoc-gf-disk-raw n
          , Raw-Tm (TmTyped.tm (assoc-wᵀ n)) ⟩
        ]T
      ≡ Raw-Ty (MorTy (assoc-zᵀ n) (assoc-wᵀ n))
  assoc-src-drop-top-type-imageᵀ n =
    trans
      (cong
        (λ A₀ →
          Raw.[ A₀ ]
            (Raw.wkTm
              {A = Whisk.W.varps-to-type (Whisk.comp-mid n)}
              (Raw.var (Whisk.W.varps-to-var (Whisk.comp-mid n)))
              Raw.[
                Raw.⟨
                  assoc-gf-disk-raw n
                , Raw-Tm (TmTyped.tm (assoc-wᵀ n)) ⟩
              ]t)
            ⇒ Raw-Tm (TmTyped.tm (assoc-wᵀ n)))
        (Raw.wkTy-[]T
          (Whisk.W.varps-to-type (Whisk.comp-mid n))
          (assoc-gf-disk-raw n)
          (Raw-Tm (TmTyped.tm (assoc-wᵀ n)))))
      (trans
        (cong
          (λ s →
            Raw.[
              Whisk.W.varps-to-type (Whisk.comp-mid n)
                Raw.[ assoc-gf-disk-raw n ]T
            ]
              s
              ⇒ Raw-Tm (TmTyped.tm (assoc-wᵀ n)))
          (Raw.wkTm-[]t
            {A = Whisk.W.varps-to-type (Whisk.comp-mid n)}
            (Raw.var (Whisk.W.varps-to-var (Whisk.comp-mid n)))
            (assoc-gf-disk-raw n)
            (Raw-Tm (TmTyped.tm (assoc-wᵀ n)))))
        (trans
          (cong
            (λ A₀ →
              Raw.[ A₀ ]
                (Raw.lookup (Whisk.W.varps-to-var (Whisk.comp-mid n)) (assoc-gf-disk-raw n))
                ⇒ Raw-Tm (TmTyped.tm (assoc-wᵀ n)))
            (assoc-gf-disk-mid-type-imageᵀ n))
          (cong
            (λ s →
              Raw.[ Raw-Ty (assoc-baseᵀ n) ]
                s
                ⇒ Raw-Tm (TmTyped.tm (assoc-wᵀ n)))
            (assoc-gf-disk-mid-imageᵀ n))))

assoc-src-drop-top-typed : (n : ℕ)
  → tyOf (TmTyped.tm (assoc-hᵀ n))
    ≡
      [ wkTy (varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n)) ]
        vs (Whisk.W.varps-to-var (Whisk.comp-mid n))
        ⇒ vz :[ refl , refl ]
      [ assoc-src-drop-step n ]T
assoc-src-drop-top-typed n =
  trans
    (TmTyped.tp (assoc-hᵀ n))
    (sym (Ty-ext (assoc-src-drop-top-type-imageᵀ n)))

assoc-src-drop-built :
  (n : ℕ)
  → Sub
      (Γ-assocᵀ n)
      ((Whisk.Γ-disk (suc n) ▸ varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n))
        ▸
        [ wkTy (varps-to-type {Γ = Whisk.Γ-disk (suc n)} (Whisk.comp-mid n)) ]
          vs (Whisk.W.varps-to-var (Whisk.comp-mid n))
          ⇒ vz :[ refl , refl ])
assoc-src-drop-built n =
  ⟨ assoc-src-drop-step n , TmTyped.tm (assoc-hᵀ n) ⟩:[ assoc-src-drop-top-typed n ]

assoc-src-drop :
  (n : ℕ)
  → Sub (Γ-assocᵀ n) (Whisk.Γ-comp n)
assoc-src-drop n =
  mkSub (assoc-src-drop-raw n) (Sub-wf (assoc-src-drop-built n))

abstract
  assoc-src-drop-comp-ty-image : (n : ℕ)
    → Whisk.W.Γ-comp-ty-raw n Raw.[ assoc-src-drop-raw n ]T
      ≡ Raw-Ty (assoc-baseᵀ n)
  assoc-src-drop-comp-ty-image n =
    trans
      (cong
        (λ A₀ → A₀ Raw.[ assoc-src-drop-raw n ]T)
        (Whisk.W.Γ-comp-ty-raw-match n))
      (trans
        (Raw.wkTy-[]T
          (Raw.wkTy (Whisk.W.varps-to-type (Whisk.comp-mid n)))
          (Raw.⟨
            assoc-gf-disk-raw n
          , Raw-Tm (TmTyped.tm (assoc-wᵀ n)) ⟩)
          (Raw-Tm (TmTyped.tm (assoc-hᵀ n))))
        (trans
          (Raw.wkTy-[]T
            (Whisk.W.varps-to-type (Whisk.comp-mid n))
            (assoc-gf-disk-raw n)
            (Raw-Tm (TmTyped.tm (assoc-wᵀ n))))
          (assoc-gf-disk-mid-type-imageᵀ n)))

abstract
  assoc-src-drop-comp-src-image : (n : ℕ)
    → Whisk.W.Γ-comp-src-raw n Raw.[ assoc-src-drop-raw n ]t
      ≡ Raw-Tm (TmTyped.tm (assoc-xᵀ n))
  assoc-src-drop-comp-src-image n =
    trans
      (cong
        (λ t → t Raw.[ assoc-src-drop-raw n ]t)
        (Whisk.W.Γ-comp-src-raw-match n))
      (assoc-gf-src-disk-cell-imageᵀ n)

abstract
  assoc-src-drop-comp-tgt-image : (n : ℕ)
    → Whisk.W.Γ-comp-tgt-raw n Raw.[ assoc-src-drop-raw n ]t
      ≡ Raw-Tm (TmTyped.tm (assoc-wᵀ n))
  assoc-src-drop-comp-tgt-image n =
    trans
      (cong
        (λ t → t Raw.[ assoc-src-drop-raw n ]t)
        (Whisk.W.Γ-comp-tgt-raw-match n))
      refl

abstract
  assoc-srcᵀ-type-image : (n : ℕ)
    → Raw-Ty (Whisk.right-whisker-ty-univ n 0 [ assoc-src-drop n ]T)
      ≡ Raw-Ty (MorTy (assoc-xᵀ n) (assoc-wᵀ n))
  assoc-srcᵀ-type-image n =
    trans
      (cong
        (λ A₀ → A₀ Raw.[ Raw-Sub (assoc-src-drop n) ]T)
        (Whisk.right-whisker-ty-univ0-raw n))
      (trans
        (cong
          (λ A₀ → A₀ Raw.[ Raw-Sub (assoc-src-drop n) ]T)
          (Whisk.W.Γ-comp-univ-ty-raw-match n))
        (trans
          (cong
            (λ A₀ →
              Raw.[ A₀ ]
                (Whisk.W.Γ-comp-src-raw n Raw.[ Raw-Sub (assoc-src-drop n) ]t)
                ⇒
                (Whisk.W.Γ-comp-tgt-raw n Raw.[ Raw-Sub (assoc-src-drop n) ]t))
            (assoc-src-drop-comp-ty-image n))
          (trans
            (cong
              (λ s →
                Raw.[ Raw-Ty (assoc-baseᵀ n) ]
                  s
                  ⇒
                  (Whisk.W.Γ-comp-tgt-raw n Raw.[ Raw-Sub (assoc-src-drop n) ]t))
              (assoc-src-drop-comp-src-image n))
            (cong
              (λ t →
                Raw.[ Raw-Ty (assoc-baseᵀ n) ]
                  (Raw-Tm (TmTyped.tm (assoc-xᵀ n)))
                  ⇒ t)
              (assoc-src-drop-comp-tgt-image n)))))

assoc-srcᵀ-tm : (n : ℕ) → Tm (Γ-assocᵀ n)
assoc-srcᵀ-tm n =
  Whisk.right-whisker-tm-univ n 0 [ assoc-src-drop n ]t

abstract
  assoc-srcᵀ-typed : (n : ℕ)
    → tyOf (assoc-srcᵀ-tm n) ≡ MorTy (assoc-xᵀ n) (assoc-wᵀ n)
  assoc-srcᵀ-typed n =
    trans
      (tyOfSub
        {t = Whisk.right-whisker-tm-univ n 0}
        {A = Whisk.right-whisker-ty-univ n 0}
        {σ = assoc-src-drop n}
        (Whisk.right-whisker-tm-typed-univ n 0))
      (Ty-ext (assoc-srcᵀ-type-image n))

assoc-srcᵀ : (n : ℕ) → MorTm (assoc-xᵀ n) (assoc-wᵀ n)
assoc-srcᵀ n = mk (assoc-srcᵀ-tm n) (assoc-srcᵀ-typed n)

abstract
  assoc-tgtᵀ-type-image : (n : ℕ)
    → Raw-Ty (Whisk.right-whisker-ty-univ n 0 [ assoc-tgt-drop n ]T)
      ≡ Raw-Ty (MorTy (assoc-xᵀ n) (assoc-wᵀ n))
  assoc-tgtᵀ-type-image n =
    trans
      (cong
        (λ A₀ → A₀ Raw.[ Raw-Sub (assoc-tgt-drop n) ]T)
        (Whisk.right-whisker-ty-univ0-raw n))
      (trans
        (cong
          (λ A₀ → A₀ Raw.[ Raw-Sub (assoc-tgt-drop n) ]T)
          (Whisk.W.Γ-comp-univ-ty-raw-match n))
        (trans
          (cong
            (λ A₀ →
              Raw.[ A₀ ]
                (Whisk.W.Γ-comp-src-raw n Raw.[ Raw-Sub (assoc-tgt-drop n) ]t)
                ⇒
                (Whisk.W.Γ-comp-tgt-raw n Raw.[ Raw-Sub (assoc-tgt-drop n) ]t))
            (assoc-tgt-drop-comp-ty-image n))
          (trans
            (cong
              (λ s →
                Raw.[ Raw-Ty (assoc-baseᵀ n) ]
                  s
                  ⇒
                  (Whisk.W.Γ-comp-tgt-raw n Raw.[ Raw-Sub (assoc-tgt-drop n) ]t))
              (assoc-tgt-drop-comp-src-image n))
            (cong
              (λ t →
                Raw.[ Raw-Ty (assoc-baseᵀ n) ]
                  (Raw-Tm (TmTyped.tm (assoc-xᵀ n)))
                  ⇒ t)
              (assoc-tgt-drop-comp-tgt-image n)))))

assoc-tgtᵀ-tm : (n : ℕ) → Tm (Γ-assocᵀ n)
assoc-tgtᵀ-tm n =
  Whisk.right-whisker-tm-univ n 0 [ assoc-tgt-drop n ]t

abstract
  assoc-tgtᵀ-typed : (n : ℕ)
    → tyOf (assoc-tgtᵀ-tm n) ≡ MorTy (assoc-xᵀ n) (assoc-wᵀ n)
  assoc-tgtᵀ-typed n =
    trans
      (tyOfSub
        {t = Whisk.right-whisker-tm-univ n 0}
        {A = Whisk.right-whisker-ty-univ n 0}
        {σ = assoc-tgt-drop n}
        (Whisk.right-whisker-tm-typed-univ n 0))
      (Ty-ext (assoc-tgtᵀ-type-image n))

assoc-tgtᵀ : (n : ℕ) → MorTm (assoc-xᵀ n) (assoc-wᵀ n)
assoc-tgtᵀ n = mk (assoc-tgtᵀ-tm n) (assoc-tgtᵀ-typed n)

abstract
  assoc-tgt : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → MorTm x w
  assoc-tgt {A = A} {x = x} {y = y} {z = z} {w = w} f g h =
    comp
      {A = A}
      {x = x}
      {y = y}
      {z = w}
      (comp
        {A = A}
        {x = y}
        {y = z}
        {z = w}
          h
          g)
      f

abstract
  assoc-tgt-raw : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Tm (TmTyped.tm (assoc-tgt f g h))
      ≡ Raw-Tm
          (TmTyped.tm
            (comp
              {A = A}
              {x = x}
              {y = y}
              {z = w}
              (comp
                {A = A}
                {x = y}
                {y = z}
                {z = w}
                h
                g)
              f))
  assoc-tgt-raw f g h = refl

assoc-qᶠ : {Γ : Ctx} {A : Ty Γ} {x y : TmTyped A}
  → (f : MorTm x y)
  → Whisk.itgt
      (Whisk.homTy A
        (TmTyped.tm x)
        (TmTyped.tm y)
        (TmTyped.tp x)
        (TmTyped.tp y))
      (TmTyped.tm y)
assoc-qᶠ {x = x} {y = y} f = Whisk.itgt-base (TmTyped.tp x) (TmTyped.tp y)

assoc-σfg : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
  → (f : MorTm x y) → (g : MorTm y z)
  → Sub Γ (Whisk.Γ-comp (dim-ty A))
assoc-σfg {x = x} {y = y} {z = z} f g =
  Whisk.γ-rwhisk
    (TmTyped.tp y)
    (TmTyped.tp z)
    (mor-tp-whisk g)
    (mor-tp-whisk f)
    (assoc-qᶠ f)


assoc-σfg-disk-dim : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
  → (f : MorTm x y) → (g : MorTm y z)
  → dim-ty (MorTy x y) ≡ suc (dim-ty A)
assoc-σfg-disk-dim {y = y} f g =
  Whisk.itgt-dim (TmTyped.tp y) (assoc-qᶠ f)

assoc-σfg-disk : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
  → (f : MorTm x y) → (g : MorTm y z)
  → Sub Γ (Whisk.Γ-disk (suc (dim-ty A)))
assoc-σfg-disk {A = A} f g =
  Whisk.γ-disk-cast
    (suc (dim-ty A))
    (assoc-σfg-disk-dim f g)
    (mor-tp-whisk f)

assoc-σfg-disk-uip : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
  → (f : MorTm x y) → (g : MorTm y z)
  → Raw-Sub (assoc-σfg-disk f g)
    ≡ Raw-Sub (Whisk.γ-disk-cast (suc (dim-ty A)) refl (mor-tp-whisk f))
assoc-σfg-disk-uip {A = A} f g =
  cong
    (λ e → Raw-Sub (Whisk.γ-disk-cast (suc (dim-ty A)) e (mor-tp-whisk f)))
    (uip (assoc-σfg-disk-dim f g) refl)

assoc-σfg-raw-match : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
  → (f : MorTm x y) → (g : MorTm y z)
  → Raw-Sub (assoc-σfg f g)
    ≡ Raw.⟨
        Raw.⟨ Raw-Sub (assoc-σfg-disk f g) , Raw-Tm (TmTyped.tm z) ⟩
      , Raw-Tm (TmTyped.tm g) ⟩
assoc-σfg-raw-match f g = refl

abstract
  assoc-σfg-base-image : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z)
    → Raw-Ty (assoc-z-tyᵀ (dim-ty A) [ assoc-σfg f g ]T)
      ≡ Raw-Ty A
  assoc-σfg-base-image {A = A} {y = y} {z = z} f g =
    trans
      (Raw.wkTy-[]T
        (Raw.wkTy (Whisk.W.varps-to-type (Whisk.comp-mid (dim-ty A))))
        (Raw.⟨ Raw-Sub (assoc-σfg-disk f g) , Raw-Tm (TmTyped.tm z) ⟩)
        (Raw-Tm (TmTyped.tm g)))
      (trans
        (Raw.wkTy-[]T
          (Whisk.W.varps-to-type (Whisk.comp-mid (dim-ty A)))
          (Raw-Sub (assoc-σfg-disk f g))
          (Raw-Tm (TmTyped.tm z)))
        (Whisk.rwhisk-mid-type-image
          (TmTyped.tp y)
          (mor-tp-whisk f)
          (assoc-qᶠ f)))

assoc-σw-typed : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
  → (f : MorTm x y) → (g : MorTm y z)
  → tyOf (TmTyped.tm w)
    ≡ assoc-z-tyᵀ (dim-ty A) [ assoc-σfg f g ]T
assoc-σw-typed {w = w} f g =
  trans (TmTyped.tp w) (sym (Ty-ext (assoc-σfg-base-image f g)))

assoc-σw : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
  → (f : MorTm x y) → (g : MorTm y z)
  → Sub Γ (Whisk.Γ-comp (dim-ty A) ▸ assoc-z-tyᵀ (dim-ty A))
assoc-σw {A = A} {w = w} f g =
  ⟨_,_⟩:[_]
    (assoc-σfg f g)
    {A = assoc-z-tyᵀ (dim-ty A)}
    (TmTyped.tm w)
    (assoc-σw-typed {A = A} {w = w} f g)

abstract
  assoc-drop-σfg : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Sub (assoc-drop (dim-ty A))
        Raw.∘ Raw.⟨ Raw-Sub (assoc-σw {w = w} f g) , Raw-Tm (TmTyped.tm h) ⟩
      ≡ Raw-Sub (assoc-σfg f g)
  assoc-drop-σfg {A = A} {w = w} f g h =
    trans
      (Raw.wkSub-∘
        (Raw.wkSub (Raw.idS (Raw-Ctx (Whisk.Γ-comp (dim-ty A)))))
        (Raw-Sub (assoc-σw {w = w} f g))
        (Raw-Tm (TmTyped.tm h)))
      (trans
        (Raw.wkSub-∘
          (Raw.idS (Raw-Ctx (Whisk.Γ-comp (dim-ty A))))
          (Raw-Sub (assoc-σfg f g))
          (Raw-Tm (TmTyped.tm w)))
        (Raw.∘-idS-l (Raw-Sub (assoc-σfg f g))))

abstract
  assoc-σfg-z-image : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z)
    → Raw.lookup (Whisk.W.varps-to-var (assoc-zps (dim-ty A))) (Raw-Sub (assoc-σfg f g))
      ≡ Raw-Tm (TmTyped.tm z)
  assoc-σfg-z-image f g = refl

abstract
  assoc-σfg-x-image : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z)
    → Raw.lookup (Whisk.comp-src-var (dim-ty A)) (Raw-Sub (assoc-σfg f g))
      ≡ Raw-Tm (TmTyped.tm x)
  assoc-σfg-x-image {A = A} {x = x} {y = y} f g =
    trans
      (cong
        (λ σ → Raw.lookup (Whisk.disk-src-var (dim-ty A)) σ)
        (assoc-σfg-disk-uip f g))
      (Whisk.γ-disk-cast-src-image
        (TmTyped.tp x)
        (TmTyped.tp y)
        (mor-tp-whisk f))

abstract
  assoc-σfg-disk-src-comp : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z)
    → Whisk.W.disk-prev-src-raw (dim-ty A) Raw.∘ Raw-Sub (assoc-σfg-disk f g)
      ≡ Raw-Sub (Whisk.γ-disk-cast (dim-ty A) refl (TmTyped.tp x))
  assoc-σfg-disk-src-comp {A = A} {x = x} {y = y} f g =
    trans
      (cong
        (λ σ → Whisk.W.disk-prev-src-raw (dim-ty A) Raw.∘ σ)
        (assoc-σfg-disk-uip f g))
      (Whisk.γ-disk-src-comp
        (TmTyped.tp x)
        (TmTyped.tp y)
        (mor-tp-whisk f)
        (dim-ty A)
        refl)

abstract
  assoc-σfg-disk-tgt-comp : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z)
    → Whisk.W.disk-prev-tgt-raw (dim-ty A) Raw.∘ Raw-Sub (assoc-σfg-disk f g)
      ≡ Raw-Sub (Whisk.γ-disk-cast (dim-ty A) refl (TmTyped.tp y))
  assoc-σfg-disk-tgt-comp {A = A} {x = x} {y = y} f g =
    trans
      (cong
        (λ σ → Whisk.W.disk-prev-tgt-raw (dim-ty A) Raw.∘ σ)
        (assoc-σfg-disk-uip f g))
      (Whisk.γ-disk-tgt-comp
        (TmTyped.tp x)
        (TmTyped.tp y)
        (mor-tp-whisk f)
        (dim-ty A)
        refl)

abstract
  assoc-σhg-disk-match : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Sub (Whisk.γ-disk-cast (suc (dim-ty A)) refl (mor-tp-whisk g))
      ≡ Raw.⟨
          Raw.⟨
            Whisk.W.disk-prev-tgt-raw (dim-ty A) Raw.∘ Raw-Sub (assoc-σfg-disk f g)
          , Raw-Tm (TmTyped.tm z) ⟩
        , Raw-Tm (TmTyped.tm g) ⟩
  assoc-σhg-disk-match {A = A} {y = y} {z = z} f g h =
    trans
      (Whisk.γ-disk-cast-hom-raw
        (TmTyped.tp y)
        (TmTyped.tp z)
        (mor-tp-whisk g)
        (dim-ty A)
        refl)
      (cong
        (λ σ →
          Raw.⟨ Raw.⟨ σ , Raw-Tm (TmTyped.tm z) ⟩ , Raw-Tm (TmTyped.tm g) ⟩)
        (sym (assoc-σfg-disk-tgt-comp f g)))

abstract
  assoc-σfg-tgt-image : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z)
    → Raw.lookup (Whisk.comp-tgt-var (dim-ty A)) (Raw-Sub (assoc-σfg f g))
      ≡ Raw-Tm (TmTyped.tm z)
  assoc-σfg-tgt-image f g = refl

abstract
  assoc-σw-H-image : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z)
    → Raw-Ty (assoc-Hᵀ (dim-ty A) [ assoc-σw {w = w} f g ]T)
      ≡ Raw-Ty (MorTy z w)
  assoc-σw-H-image {A = A} {z = z} {w = w} f g =
    Whisk.ext-cell-ty-snoc-raw
      (assoc-zps (dim-ty A))
      (assoc-σfg-z-image f g)
      (assoc-σfg-base-image f g)

assoc-σh-typed : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
  → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
  → tyOf (TmTyped.tm h) ≡ assoc-Hᵀ (dim-ty A) [ assoc-σw {w = w} f g ]T
assoc-σh-typed {z = z} {w = w} f g h =
  trans (TmTyped.tp h) (sym (Ty-ext (assoc-σw-H-image {z = z} {w = w} f g)))

assoc-σ : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
  → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
  → Sub Γ (Γ-assocᵀ (dim-ty A))
assoc-σ {w = w} f g h =
  ⟨ assoc-σw {w = w} f g , TmTyped.tm h ⟩:[ assoc-σh-typed f g h ]

abstract
  assoc-f-disk-raw-σ : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → assoc-f-disk-raw (dim-ty A) Raw.∘ Raw-Sub (assoc-σ f g h)
      ≡ Raw-Sub (assoc-σfg-disk f g)
  assoc-f-disk-raw-σ {A = A} {z = z} {w = w} f g h =
    trans
      (sym
        (Raw.assocS
          (Whisk.Γ-comp-disk-raw (dim-ty A))
          (Raw-Sub (assoc-drop (dim-ty A)))
          (Raw-Sub (assoc-σ f g h))))
      (trans
        (cong
          (λ σ → Whisk.Γ-comp-disk-raw (dim-ty A) Raw.∘ σ)
          (assoc-drop-σfg {w = w} f g h))
        (trans
          (cong
            (λ σ → Whisk.Γ-comp-disk-raw (dim-ty A) Raw.∘ σ)
            (assoc-σfg-raw-match f g))
          (trans
            (Raw.wkSub-∘
              (Raw.wkSub
                (Raw.idS (Whisk.W.Γ-disk (suc (dim-ty A)))))
              (Raw.⟨
                Raw-Sub (assoc-σfg-disk f g)
              , Raw-Tm (TmTyped.tm z) ⟩)
              (Raw-Tm (TmTyped.tm g)))
            (trans
              (Raw.wkSub-∘
                (Raw.idS (Whisk.W.Γ-disk (suc (dim-ty A))))
                (Raw-Sub (assoc-σfg-disk f g))
                (Raw-Tm (TmTyped.tm z)))
              (Raw.∘-idS-l (Raw-Sub (assoc-σfg-disk f g)))))))

abstract
  assoc-g-src-disk-raw-σ : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → assoc-g-src-disk-raw (dim-ty A) Raw.∘ Raw-Sub (assoc-σ f g h)
      ≡ Whisk.W.disk-prev-tgt-raw (dim-ty A) Raw.∘ Raw-Sub (assoc-σfg-disk f g)
  assoc-g-src-disk-raw-σ {A = A} f g h =
    trans
      (sym
        (Raw.assocS
          (Whisk.W.disk-prev-tgt-raw (dim-ty A))
          (assoc-f-disk-raw (dim-ty A))
          (Raw-Sub (assoc-σ f g h))))
      (cong
        (λ σ → Whisk.W.disk-prev-tgt-raw (dim-ty A) Raw.∘ σ)
        (assoc-f-disk-raw-σ f g h))

abstract
  assoc-base-image : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Ty (assoc-baseᵀ (dim-ty A) [ assoc-σ f g h ]T)
      ≡ Raw-Ty A
  assoc-base-image {A = A} {w = w} f g h =
    trans
      (Raw.wkTy-[]T
        (Raw.wkTy (Raw-Ty (assoc-z-tyᵀ (dim-ty A))))
        (Raw-Sub (assoc-σw {w = w} f g))
        (Raw-Tm (TmTyped.tm h)))
      (trans
        (Raw.wkTy-[]T
          (Raw-Ty (assoc-z-tyᵀ (dim-ty A)))
          (Raw-Sub (assoc-σfg f g))
          (Raw-Tm (TmTyped.tm w)))
        (assoc-σfg-base-image f g))

abstract
  assoc-x-image : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Tm (TmTyped.tm (assoc-xᵀ (dim-ty A))) Raw.[ Raw-Sub (assoc-σ f g h) ]t
      ≡ Raw-Tm (TmTyped.tm x)
  assoc-x-image f g h = assoc-σfg-x-image f g

abstract
  assoc-z-image : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Tm (TmTyped.tm (assoc-zᵀ (dim-ty A))) Raw.[ Raw-Sub (assoc-σ f g h) ]t
      ≡ Raw-Tm (TmTyped.tm z)
  assoc-z-image f g h = assoc-σfg-tgt-image f g

abstract
  assoc-w-image : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Tm (TmTyped.tm (assoc-wᵀ (dim-ty A))) Raw.[ Raw-Sub (assoc-σ f g h) ]t
      ≡ Raw-Tm (TmTyped.tm w)
  assoc-w-image f g h = refl

abstract
  assoc-g-image : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Tm (TmTyped.tm (assoc-gᵀ (dim-ty A))) Raw.[ Raw-Sub (assoc-σ f g h) ]t
      ≡ Raw-Tm (TmTyped.tm g)
  assoc-g-image f g h = refl

abstract
  assoc-g-disk-raw-σ : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → assoc-g-disk-raw (dim-ty A) Raw.∘ Raw-Sub (assoc-σ f g h)
      ≡ Raw-Sub (Whisk.γ-disk-cast (suc (dim-ty A)) refl (mor-tp-whisk g))
  assoc-g-disk-raw-σ {A = A} f g h =
    trans
      (cong₂
        Raw.⟨_,_⟩
        (cong₂
          Raw.⟨_,_⟩
          (assoc-g-src-disk-raw-σ f g h)
          (assoc-z-image f g h))
        (assoc-g-image f g h))
      (sym (assoc-σhg-disk-match f g h))

abstract
  assoc-h-image : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Tm (TmTyped.tm (assoc-hᵀ (dim-ty A))) Raw.[ Raw-Sub (assoc-σ f g h) ]t
      ≡ Raw-Tm (TmTyped.tm h)
  assoc-h-image f g h = refl

abstract
  assoc-hg-drop-σ : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Sub (assoc-hg-drop (dim-ty A)) Raw.∘ Raw-Sub (assoc-σ f g h)
      ≡ Raw-Sub (assoc-σfg g h)
  assoc-hg-drop-σ {A = A} {w = w} f g h =
    trans
      (cong₂
        Raw.⟨_,_⟩
        (cong₂
          Raw.⟨_,_⟩
          (assoc-g-disk-raw-σ f g h)
          (assoc-w-image f g h))
        (assoc-h-image f g h))
      (trans
        (cong
          (λ σ →
            Raw.⟨
              Raw.⟨ σ , Raw-Tm (TmTyped.tm w) ⟩
            , Raw-Tm (TmTyped.tm h) ⟩)
          (sym (assoc-σfg-disk-uip g h)))
        (sym (assoc-σfg-raw-match g h)))

abstract
  assoc-hg-image : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Tm (assoc-hgᵀ-tm (dim-ty A)) Raw.[ Raw-Sub (assoc-σ f g h) ]t
      ≡ Raw-Tm
          (TmTyped.tm
            (comp
              {A = A}
              {x = y}
              {y = z}
              {z = w}
              h
              g))
  assoc-hg-image {A = A} f g h =
    trans
      (sym
        (Raw.[∘]t
          (Raw-Tm (Whisk.right-whisker-tm-univ (dim-ty A) 0))
          (Raw-Sub (assoc-hg-drop (dim-ty A)))
          (Raw-Sub (assoc-σ f g h))))
      (trans
        (cong
          (λ σ →
            Raw-Tm (Whisk.right-whisker-tm-univ (dim-ty A) 0)
              Raw.[ σ ]t)
          (assoc-hg-drop-σ f g h))
        (sym (comp-raw h g)))

abstract
  assoc-tgt-drop-σ : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Sub (assoc-tgt-drop (dim-ty A)) Raw.∘ Raw-Sub (assoc-σ f g h)
      ≡ Raw-Sub (assoc-σfg f (comp h g))
  assoc-tgt-drop-σ {A = A} {w = w} f g h =
    trans
      (cong₂
        Raw.⟨_,_⟩
        (cong₂
          Raw.⟨_,_⟩
          (assoc-f-disk-raw-σ f g h)
          (assoc-w-image f g h))
        (assoc-hg-image f g h))
      (trans
        (cong
          (λ σ →
            Raw.⟨
              Raw.⟨ σ , Raw-Tm (TmTyped.tm w) ⟩
            , Raw-Tm (TmTyped.tm (comp h g)) ⟩)
          (trans
            (assoc-σfg-disk-uip f g)
            (sym (assoc-σfg-disk-uip f (comp h g)))))
        (sym (assoc-σfg-raw-match f (comp h g))))

abstract
  assoc-gf-image : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Tm (assoc-gfᵀ-tm (dim-ty A)) Raw.[ Raw-Sub (assoc-σ f g h) ]t
      ≡ Raw-Tm
          (TmTyped.tm
            (comp
              {A = A}
              {x = x}
              {y = y}
              {z = z}
              g
              f))
  assoc-gf-image {A = A} {w = w} f g h =
    trans
      (sym
        (Raw.[∘]t
          (Raw-Tm (Whisk.right-whisker-tm-univ (dim-ty A) 0))
          (Raw-Sub (assoc-drop (dim-ty A)))
          (Raw-Sub (assoc-σ f g h))))
      (trans
        (cong
          (λ σ →
            Raw-Tm (Whisk.right-whisker-tm-univ (dim-ty A) 0)
              Raw.[ σ ]t)
          (assoc-drop-σfg {w = w} f g h))
        (sym (comp-raw {A = A} g f)))

abstract
  assoc-gf-src-disk-raw-σ : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → assoc-gf-src-disk-raw (dim-ty A) Raw.∘ Raw-Sub (assoc-σ f g h)
      ≡ Whisk.W.disk-prev-src-raw (dim-ty A) Raw.∘ Raw-Sub (assoc-σfg-disk f g)
  assoc-gf-src-disk-raw-σ {A = A} f g h =
    trans
      (sym
        (Raw.assocS
          (Whisk.W.disk-prev-src-raw (dim-ty A))
          (assoc-f-disk-raw (dim-ty A))
          (Raw-Sub (assoc-σ f g h))))
      (cong
        (λ σ → Whisk.W.disk-prev-src-raw (dim-ty A) Raw.∘ σ)
        (assoc-f-disk-raw-σ f g h))

abstract
  assoc-σgf-disk-match : {Γ : Ctx} {A : Ty Γ} {x y z : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (gf : MorTm x z)
    → Raw-Sub (Whisk.γ-disk-cast (suc (dim-ty A)) refl (mor-tp-whisk gf))
      ≡ Raw.⟨
          Raw.⟨
            Whisk.W.disk-prev-src-raw (dim-ty A) Raw.∘ Raw-Sub (assoc-σfg-disk f g)
          , Raw-Tm (TmTyped.tm z) ⟩
        , Raw-Tm (TmTyped.tm gf) ⟩
  assoc-σgf-disk-match {A = A} {x = x} {z = z} f g gf =
    trans
      (Whisk.γ-disk-cast-hom-raw
        (TmTyped.tp x)
        (TmTyped.tp z)
        (mor-tp-whisk gf)
        (dim-ty A)
        refl)
      (cong
        (λ σ →
          Raw.⟨
            Raw.⟨ σ , Raw-Tm (TmTyped.tm z) ⟩
          , Raw-Tm (TmTyped.tm gf) ⟩)
        (sym (assoc-σfg-disk-src-comp f g)))

abstract
  assoc-gf-disk-raw-σ : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → (gf : MorTm x z)
    → Raw-Tm (assoc-gfᵀ-tm (dim-ty A)) Raw.[ Raw-Sub (assoc-σ f g h) ]t
      ≡ Raw-Tm (TmTyped.tm gf)
    → assoc-gf-disk-raw (dim-ty A) Raw.∘ Raw-Sub (assoc-σ f g h)
      ≡ Raw-Sub (Whisk.γ-disk-cast (suc (dim-ty A)) refl (mor-tp-whisk gf))
  assoc-gf-disk-raw-σ f g h gf gf-image =
    trans
      (cong₂
        Raw.⟨_,_⟩
        (cong₂
          Raw.⟨_,_⟩
          (assoc-gf-src-disk-raw-σ f g h)
          (assoc-z-image f g h))
        gf-image)
      (sym (assoc-σgf-disk-match f g gf))

abstract
  assoc-src-drop-σ : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → (gf : MorTm x z)
    → Raw-Tm (assoc-gfᵀ-tm (dim-ty A)) Raw.[ Raw-Sub (assoc-σ f g h) ]t
      ≡ Raw-Tm (TmTyped.tm gf)
    → Raw-Sub (assoc-src-drop (dim-ty A)) Raw.∘ Raw-Sub (assoc-σ f g h)
      ≡ Raw-Sub (assoc-σfg gf h)
  assoc-src-drop-σ {w = w} f g h gf gf-image =
    trans
      (cong₂
        Raw.⟨_,_⟩
        (cong₂
          Raw.⟨_,_⟩
          (assoc-gf-disk-raw-σ f g h gf gf-image)
          (assoc-w-image f g h))
        (assoc-h-image f g h))
      (trans
        (cong
          (λ σ →
            Raw.⟨
              Raw.⟨ σ , Raw-Tm (TmTyped.tm w) ⟩
            , Raw-Tm (TmTyped.tm h) ⟩)
          (sym (assoc-σfg-disk-uip gf h)))
        (sym (assoc-σfg-raw-match gf h)))

abstract
  assoc-mor-base-image : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Ty
        (MorTy (assoc-xᵀ (dim-ty A)) (assoc-wᵀ (dim-ty A))
          [ assoc-σ f g h ]T)
      ≡ Raw-Ty (MorTy x w)
  assoc-mor-base-image {A = A} {x = x} {w = w} f g h =
    trans
      (cong
        (λ A₀ →
          Raw.[ A₀ ]
            (Raw-Tm (TmTyped.tm (assoc-xᵀ (dim-ty A))) Raw.[ Raw-Sub (assoc-σ f g h) ]t)
            ⇒
            (Raw-Tm (TmTyped.tm (assoc-wᵀ (dim-ty A))) Raw.[ Raw-Sub (assoc-σ f g h) ]t))
        (assoc-base-image f g h))
      (trans
        (cong
          (λ s →
            Raw.[ Raw-Ty A ]
              s
              ⇒
              (Raw-Tm (TmTyped.tm (assoc-wᵀ (dim-ty A))) Raw.[ Raw-Sub (assoc-σ f g h) ]t))
          (assoc-x-image f g h))
        (cong
          (λ t →
            Raw.[ Raw-Ty A ]
              (Raw-Tm (TmTyped.tm x))
              ⇒ t)
          (assoc-w-image f g h)))

assoc-src-tm : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
  → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
  → Tm Γ
assoc-src-tm {A = A} f g h =
  assoc-srcᵀ-tm (dim-ty A) [ assoc-σ f g h ]t

abstract
  assoc-src-sub-ty-raw : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw.tyOf (Raw-Tm (assoc-src-tm f g h))
      ≡ Raw-Ty
          (MorTy (assoc-xᵀ (dim-ty A)) (assoc-wᵀ (dim-ty A))
            [ assoc-σ f g h ]T)
  assoc-src-sub-ty-raw {A = A} f g h =
    trans
      (tyOf-comm
        (Raw-Tm (assoc-srcᵀ-tm (dim-ty A)))
        (Raw-Ty (MorTy (assoc-xᵀ (dim-ty A)) (assoc-wᵀ (dim-ty A))))
        (cast-sub (assoc-σ f g h))
        (trans
          (tyOf-from-tyOf (assoc-srcᵀ-tm (dim-ty A)))
          (cong Raw-Ty (assoc-srcᵀ-typed (dim-ty A)))))
      (sym
        (Raw-Ty-Sub
          (MorTy (assoc-xᵀ (dim-ty A)) (assoc-wᵀ (dim-ty A)))
          (assoc-σ f g h)))

abstract
  assoc-src-typed : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → tyOf (assoc-src-tm f g h) ≡ MorTy x w
  assoc-src-typed f g h =
    Ty-ext
      (trans
        (sym (tyOf-from-tyOf (assoc-src-tm f g h)))
        (trans
          (assoc-src-sub-ty-raw f g h)
          (assoc-mor-base-image f g h)))

assoc-src : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
  → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
  → MorTm x w
assoc-src f g h = mk (assoc-src-tm f g h) (assoc-src-typed f g h)

abstract
  assoc-src-image : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Tm (assoc-srcᵀ-tm (dim-ty A)) Raw.[ Raw-Sub (assoc-σ f g h) ]t
      ≡ Raw-Tm (TmTyped.tm (assoc-src f g h))
  assoc-src-image f g h = refl

abstract
  assoc-tgt-image : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Tm (assoc-tgtᵀ-tm (dim-ty A)) Raw.[ Raw-Sub (assoc-σ f g h) ]t
      ≡ Raw-Tm (TmTyped.tm (assoc-tgt f g h))
  assoc-tgt-image {A = A} f g h =
    trans
      (sym
        (Raw.[∘]t
          (Raw-Tm (Whisk.right-whisker-tm-univ (dim-ty A) 0))
          (Raw-Sub (assoc-tgt-drop (dim-ty A)))
          (Raw-Sub (assoc-σ f g h))))
      (trans
        (cong
          (λ σ →
            Raw-Tm (Whisk.right-whisker-tm-univ (dim-ty A) 0)
              Raw.[ σ ]t)
          (assoc-tgt-drop-σ f g h))
        (trans
          (sym (comp-raw (comp h g) f))
          (sym (assoc-tgt-raw f g h))))

abstract
  assoc-left-raw : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → (gf : MorTm x z)
    → Raw-Tm (assoc-gfᵀ-tm (dim-ty A)) Raw.[ Raw-Sub (assoc-σ f g h) ]t
      ≡ Raw-Tm (TmTyped.tm gf)
    → Raw-Tm (TmTyped.tm (assoc-src f g h))
      ≡ Raw-Tm (TmTyped.tm (h • gf))
  assoc-left-raw {A = A} f g h gf gf-image =
    trans
      (sym (assoc-src-image f g h))
      (trans
        (sym
          (Raw.[∘]t
            (Raw-Tm (Whisk.right-whisker-tm-univ (dim-ty A) 0))
            (Raw-Sub (assoc-src-drop (dim-ty A)))
            (Raw-Sub (assoc-σ f g h))))
        (trans
          (cong
            (λ σ → Raw-Tm (Whisk.right-whisker-tm-univ (dim-ty A) 0) Raw.[ σ ]t)
            (assoc-src-drop-σ f g h gf gf-image))
          (sym (comp-raw h gf))))

abstract
  assoc-drop-dep : (n : ℕ)
    → (x : Var (Whisk.Γ-comp n))
    → Dep.DepVarSub
        (Raw.succ (Raw.succ x))
        (Raw-Sub (assoc-drop n))
  assoc-drop-dep n x =
    Whisk.dep-sub-wk
      (Whisk.dep-sub-wk
        (idS-dep {Γ = Whisk.Γ-comp n} x))

abstract
  assoc-gfᵀ-dep : (n : ℕ)
    → (x : Var (Whisk.Γ-comp n))
    → Dep.DepVarTm
        (Raw.succ (Raw.succ x))
        (Raw-Tm (assoc-gfᵀ-tm n))
  assoc-gfᵀ-dep n x =
    Dep.dep-coh
      (subst
        (Dep.DepVarSub (Raw.succ (Raw.succ x)))
        (sym (Raw.∘-idS-l (Raw-Sub (assoc-drop n))))
        (assoc-drop-dep n x))

abstract
  assoc-gf-disk-dep : (n : ℕ)
    → (x : Var (Whisk.Γ-comp n))
    → Dep.DepVarSub
        (Raw.succ (Raw.succ x))
        (assoc-gf-disk-raw n)
  assoc-gf-disk-dep n x =
    Dep.dep-sub-here (assoc-gfᵀ-dep n x)

abstract
  assoc-src-drop-dep : (n : ℕ)
    → (x : Var (Γ-assocᵀ n))
    → Dep.DepVarSub x (Raw-Sub (assoc-src-drop n))
  assoc-src-drop-dep n Raw.zero =
    Dep.dep-sub-here (Dep.dep-var Dep.dep-refl)
  assoc-src-drop-dep n (Raw.succ Raw.zero) =
    Dep.dep-sub-there
      (Dep.dep-sub-here
        (Dep.dep-var (Dep.dep-var-var-refl (Raw.succ Raw.zero))))
  assoc-src-drop-dep n (Raw.succ (Raw.succ x)) =
    Dep.dep-sub-there (Dep.dep-sub-there (assoc-gf-disk-dep n x))

abstract
  assoc-srcᵀ-dep : (n : ℕ)
    → (x : Var (Γ-assocᵀ n))
    → Dep.DepVarTm x (Raw-Tm (assoc-srcᵀ-tm n))
  assoc-srcᵀ-dep n x =
    Dep.dep-coh
      (subst
        (Dep.DepVarSub x)
        (sym (Raw.∘-idS-l (Raw-Sub (assoc-src-drop n))))
        (assoc-src-drop-dep n x))

abstract
  assoc-fᵀ-disk-var-dep : (n : ℕ)
    → (x : Var (Whisk.Γ-disk (suc n)))
    → Dep.DepVarTm
        (Raw.succ (Raw.succ (Raw.succ (Raw.succ x))))
        (Raw-Tm (TmTyped.tm (assoc-fᵀ n)))
  assoc-fᵀ-disk-var-dep n x =
    Dep.dep-var
      (Dep.dep-weak
        (Dep.dep-weak
          (Dep.dep-weak
            (Dep.dep-weak
              (Whisk.disk-dangling-all (suc n) x)))))

abstract
  assoc-f-disk-cell-image : (n : ℕ)
    → Raw.lookup
        (Whisk.W.varps-to-var (Whisk.W.cell-dangling (suc n)))
        (assoc-f-disk-raw n)
      ≡ Raw-Tm (TmTyped.tm (assoc-fᵀ n))
  assoc-f-disk-cell-image n = refl

abstract
  assoc-f-disk-dep : (n : ℕ)
    → (x : Var (Whisk.Γ-disk (suc n)))
    → Dep.DepVarSub
        (Raw.succ (Raw.succ (Raw.succ (Raw.succ x))))
        (assoc-f-disk-raw n)
  assoc-f-disk-dep n x =
    Dep.dep-sub-at→dep-sub
      (Raw.succ (Raw.succ (Raw.succ (Raw.succ x))))
      (assoc-f-disk-raw n)
      (Whisk.W.varps-to-var (Whisk.W.cell-dangling (suc n)))
      (Dep.dep-tm-lookup→dep-sub-at
        (Raw.succ (Raw.succ (Raw.succ (Raw.succ x))))
        (assoc-f-disk-raw n)
        (Whisk.W.varps-to-var (Whisk.W.cell-dangling (suc n)))
        (subst
          (Dep.DepVarTm (Raw.succ (Raw.succ (Raw.succ (Raw.succ x)))))
          (sym (assoc-f-disk-cell-image n))
          (assoc-fᵀ-disk-var-dep n x)))

abstract
  assoc-g-disk-g-dep : (n : ℕ)
    → Dep.DepVarSub
        (Raw.succ (Raw.succ Raw.zero))
        (assoc-g-disk-raw n)
  assoc-g-disk-g-dep n =
    Dep.dep-sub-here
      (Dep.dep-var
        (Dep.dep-var-var-refl (Raw.succ (Raw.succ Raw.zero))))

abstract
  assoc-g-disk-z-dep : (n : ℕ)
    → Dep.DepVarSub
        (Raw.succ (Raw.succ (Whisk.comp-tgt-var n)))
        (assoc-g-disk-raw n)
  assoc-g-disk-z-dep n =
    Dep.dep-sub-there
      (Dep.dep-sub-here
        (Dep.dep-var
          (Dep.dep-var-var-refl (Raw.succ (Raw.succ (Whisk.comp-tgt-var n))))))

abstract
  assoc-hg-drop-h-dep : (n : ℕ)
    → Dep.DepVarSub Raw.zero (Raw-Sub (assoc-hg-drop n))
  assoc-hg-drop-h-dep n =
    Dep.dep-sub-here (Dep.dep-var Dep.dep-refl)

abstract
  assoc-hg-drop-g-dep : (n : ℕ)
    → Dep.DepVarSub
        (Raw.succ (Raw.succ Raw.zero))
        (Raw-Sub (assoc-hg-drop n))
  assoc-hg-drop-g-dep n =
    Dep.dep-sub-there (Dep.dep-sub-there (assoc-g-disk-g-dep n))

abstract
  assoc-hg-drop-z-dep : (n : ℕ)
    → Dep.DepVarSub
        (Raw.succ (Raw.succ (Whisk.comp-tgt-var n)))
        (Raw-Sub (assoc-hg-drop n))
  assoc-hg-drop-z-dep n =
    Dep.dep-sub-there (Dep.dep-sub-there (assoc-g-disk-z-dep n))

abstract
  assoc-hgᵀ-h-dep : (n : ℕ)
    → Dep.DepVarTm Raw.zero (Raw-Tm (assoc-hgᵀ-tm n))
  assoc-hgᵀ-h-dep n =
    Dep.dep-coh
      (subst
        (Dep.DepVarSub Raw.zero)
        (sym (Raw.∘-idS-l (Raw-Sub (assoc-hg-drop n))))
        (assoc-hg-drop-h-dep n))

abstract
  assoc-hgᵀ-g-dep : (n : ℕ)
    → Dep.DepVarTm
        (Raw.succ (Raw.succ Raw.zero))
        (Raw-Tm (assoc-hgᵀ-tm n))
  assoc-hgᵀ-g-dep n =
    Dep.dep-coh
      (subst
        (Dep.DepVarSub (Raw.succ (Raw.succ Raw.zero)))
        (sym (Raw.∘-idS-l (Raw-Sub (assoc-hg-drop n))))
        (assoc-hg-drop-g-dep n))

abstract
  assoc-hgᵀ-z-dep : (n : ℕ)
    → Dep.DepVarTm
        (Raw.succ (Raw.succ (Whisk.comp-tgt-var n)))
        (Raw-Tm (assoc-hgᵀ-tm n))
  assoc-hgᵀ-z-dep n =
    Dep.dep-coh
      (subst
        (Dep.DepVarSub (Raw.succ (Raw.succ (Whisk.comp-tgt-var n))))
        (sym (Raw.∘-idS-l (Raw-Sub (assoc-hg-drop n))))
        (assoc-hg-drop-z-dep n))

abstract
  assoc-tgt-drop-dep : (n : ℕ)
    → (x : Var (Γ-assocᵀ n))
    → Dep.DepVarSub x (Raw-Sub (assoc-tgt-drop n))
  assoc-tgt-drop-dep n Raw.zero =
    Dep.dep-sub-here (assoc-hgᵀ-h-dep n)
  assoc-tgt-drop-dep n (Raw.succ Raw.zero) =
    Dep.dep-sub-there
      (Dep.dep-sub-here
        (Dep.dep-var (Dep.dep-var-var-refl (Raw.succ Raw.zero))))
  assoc-tgt-drop-dep n (Raw.succ (Raw.succ Raw.zero)) =
    Dep.dep-sub-here (assoc-hgᵀ-g-dep n)
  assoc-tgt-drop-dep n (Raw.succ (Raw.succ (Raw.succ Raw.zero))) =
    Dep.dep-sub-here (assoc-hgᵀ-z-dep n)
  assoc-tgt-drop-dep n (Raw.succ (Raw.succ (Raw.succ (Raw.succ x)))) =
    Dep.dep-sub-there
      (Dep.dep-sub-there (assoc-f-disk-dep n x))

abstract
  assoc-tgtᵀ-dep : (n : ℕ)
    → (x : Var (Γ-assocᵀ n))
    → Dep.DepVarTm x (Raw-Tm (assoc-tgtᵀ-tm n))
  assoc-tgtᵀ-dep n x =
    Dep.dep-coh
      (subst
        (Dep.DepVarSub x)
        (sym (Raw.∘-idS-l (Raw-Sub (assoc-tgt-drop n))))
        (assoc-tgt-drop-dep n x))

abstract
  assoc-fullᵀ : (n : ℕ) →
    FullMod.Full
      (Γ-assocᵀ-ps n)
      (Raw-Ty (MorTy (assoc-xᵀ n) (assoc-wᵀ n)))
      (Raw-Tm (assoc-srcᵀ-tm n))
      (Raw-Tm (assoc-tgtᵀ-tm n))
  assoc-fullᵀ n =
    FullMod.full-COMPCOH
      (λ x → assoc-srcᵀ-dep n x , assoc-tgtᵀ-dep n x)

abstract
  assoc-tm : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Tm Γ
  assoc-tm {A = A} f g h =
    coh
      (Γ-assocᵀ-ps (dim-ty A))
      (MorTy (assoc-xᵀ (dim-ty A)) (assoc-wᵀ (dim-ty A)))
      (assoc-srcᵀ-tm (dim-ty A))
      (assoc-tgtᵀ-tm (dim-ty A))
      (tyOf≡→HasTy
        {t = assoc-srcᵀ-tm (dim-ty A)}
        {A = MorTy (assoc-xᵀ (dim-ty A)) (assoc-wᵀ (dim-ty A))}
        (assoc-srcᵀ-typed (dim-ty A)))
      (tyOf≡→HasTy
        {t = assoc-tgtᵀ-tm (dim-ty A)}
        {A = MorTy (assoc-xᵀ (dim-ty A)) (assoc-wᵀ (dim-ty A))}
      (assoc-tgtᵀ-typed (dim-ty A)))
      (assoc-fullᵀ (dim-ty A))
      (assoc-σ f g h)

abstract
  assoc-tm-raw : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Tm (assoc-tm f g h)
      ≡ Raw.coh
          (Raw-Ty (MorTy (assoc-xᵀ (dim-ty A)) (assoc-wᵀ (dim-ty A))))
          (Raw-Tm (assoc-srcᵀ-tm (dim-ty A)))
          (Raw-Tm (assoc-tgtᵀ-tm (dim-ty A)))
          (Raw-Sub (assoc-σ f g h))
  assoc-tm-raw f g h = refl

abstract
  assoc-type-image : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Ty (tyOf (assoc-tm f g h))
      ≡ Raw-Ty (MorTy (assoc-src f g h) (assoc-tgt f g h))
  assoc-type-image {A = A} {x = x} {w = w} f g h =
    trans
      (sym (tyOf-from-tyOf (assoc-tm f g h)))
      (trans
        (cong Raw.tyOf (assoc-tm-raw f g h))
        (trans
          (cong
            (λ A₀ →
              Raw.[ A₀ ]
                (Raw-Tm (assoc-srcᵀ-tm (dim-ty A)) Raw.[ Raw-Sub (assoc-σ f g h) ]t)
                ⇒
                (Raw-Tm (assoc-tgtᵀ-tm (dim-ty A)) Raw.[ Raw-Sub (assoc-σ f g h) ]t))
            (assoc-mor-base-image f g h))
          (trans
            (cong
              (λ s →
                Raw.[ Raw-Ty (MorTy x w) ]
                  s
                  ⇒
                  (Raw-Tm (assoc-tgtᵀ-tm (dim-ty A)) Raw.[ Raw-Sub (assoc-σ f g h) ]t))
              (assoc-src-image f g h))
            (cong
              (λ t →
                Raw.[ Raw-Ty (MorTy x w) ]
                  (Raw-Tm (TmTyped.tm (assoc-src f g h)))
                  ⇒ t)
              (assoc-tgt-image f g h)))))

```



## Direct Associativity Coherences

```agda
abstract
  assoc-direct-type-image : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → Raw-Ty (tyOf (assoc-tm f g h))
      ≡ Raw-Ty (MorTy (h • (g • f)) ((h • g) • f))
  assoc-direct-type-image {x = x} {w = w} f g h =
    trans
      (assoc-type-image f g h)
      (cong₂
        (λ s t → Raw.[ Raw-Ty (MorTy x w) ] s ⇒ t)
        (assoc-left-raw f g h (g • f) (assoc-gf-image f g h))
        (assoc-tgt-raw f g h))

opaque
  assoc : {Γ : Ctx} {A : Ty Γ} {x y z w : TmTyped A}
    → (f : MorTm x y) → (g : MorTm y z) → (h : MorTm z w)
    → MorTm (h • (g • f)) ((h • g) • f)
  assoc {Γ = Γ} {A = A} {x = x} {y = y} {z = z} {w = w} f g h =
    mk
      (assoc-tm {Γ = Γ} {A = A} {x = x} {y = y} {z = z} {w = w} f g h)
      (Ty-ext (assoc-direct-type-image {Γ = Γ} {A = A} {x = x} {y = y} {z = z} {w = w} f g h))

  assoc₁ : {Γ : Ctx} {x y z w : Obj Γ}
    → (f : Mor x y) → (g : Mor y z) → (h : Mor z w)
    → Mor₂ (h •₁ (g •₁ f)) ((h •₁ g) •₁ f)
  assoc₁ f g h =
    typed-mor2
      (subst
        (λ src → MorTm src (mor-typed ((h •₁ g) •₁ f)))
        (sym assoc₁-srcᵀ)
        (subst
          (λ tgt → MorTm (mor-typed h • (mor-typed g • mor-typed f)) tgt)
          (sym assoc₁-tgtᵀ)
          (assoc (mor-typed f) (mor-typed g) (mor-typed h))))
    where
      assoc₁-srcᵀ :
        mor-typed (h •₁ (g •₁ f)) ≡ mor-typed h • (mor-typed g • mor-typed f)
      assoc₁-srcᵀ =
        trans
          (mor-typed-•₁ (g •₁ f) h)
          (cong (λ gf → mor-typed h • gf) (mor-typed-•₁ f g))

      assoc₁-tgtᵀ :
        mor-typed ((h •₁ g) •₁ f) ≡ (mor-typed h • mor-typed g) • mor-typed f
      assoc₁-tgtᵀ =
        trans
          (mor-typed-•₁ f (h •₁ g))
          (cong (λ hg → hg • mor-typed f) (mor-typed-•₁ g h))
```
