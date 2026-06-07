# 4b-DiagramHoms-Comp: constructing the diagram hom

This is the computational companion to `4b-DiagramHoms`. The relational core gives
the *specification* `DHomOver d₁ d₂ H`. Here we construct the chosen carrier: a real
recursion building the relative diagram-hom telescope `dhom-over d₁ d₂ : DTy (Γ ▸▸ D)`,
together with the proof `dhom-over-is-DHomOver : DHomOver d₁ d₂ (dhom-over d₁ d₂)`. The
ordinary chosen hom `dhom` and its witness `dhom-is-DHom` are then derived as the
empty-source special case.

Each new hom component is built **concretely** as

```text
B  =  ↑ty (dty-sel E) A  [ dhom-over-sub-ext … ]T
```

— the naturality type of the target entry, reindexed along the diagram-hom comparison
substitution. Everything here is a genuine computed object: `↑ty`, `↑ctx-ext` and
`↑sec-ext` come from `3b-Naturality-Comp`, the endpoint weakenings
`dwkTm-fun (dhom-over d₁ d₂) aᵢ` from `4a-Diagrams-Comp`, and `B` is an actual `_[_]T`.

The comparison substitution is now **fully constructed**, not postulated. The base case
is `dhom-base-sub` (the canonical map `Γ → Γ ↑ ∅`); the recursive comparison
`dhom-over-sub d₁ d₂ : Sub ((Γ ▸▸ D) ▸▸ dhom-over d₁ d₂) (↑ctx (Γ ▸▸ E) (dty-sel E))` is
built by recursion on the two sections, with proven endpoint laws
`dhom-over-sub-left` / `dhom-over-sub-right`; and its extension across the two endpoint
variables, `dhom-over-sub-ext`, is `↑sec-ext` applied to `dhom-over-sub`, with the
endpoint typing supplied by the endpoint laws and `dwkTm-hasTySub`. There is no
remaining diagram-specific postulate in this construction.

```agda
module 4b-DiagramHoms-Comp where

open import 2a-CaTT-Comp
open import 4a-Diagrams-Comp
open import 3b-Naturality-Comp
open import 4b-DiagramHoms

import 1a-RawSyntax-Comp as Raw

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂; subst)
```

## The base comparison substitution

For the empty source/target the comparison substitution is just the canonical map
from `Γ` into its suspension along the *empty* selector `sel-∅ Γ` — there are no
diagram variables to compare yet, so every variable is copied. This is the
relational analogue of the old V10 `dhom-base-sub`. Its two section laws say the
map is a common section of both endpoint inclusions `in⁻ / in⁺`.

```agda
{-# TERMINATING #-}
mutual
  dhom-base-sub : (Γ : Ctx) → Sub Γ (↑ctx Γ (sel-∅ Γ))
  dhom-base-sub Γ with ctx-view Γ
  ... | ◆-view = ◆S
  ... | ▸-view {Γ = Γ′} A =
    let
      ρ⁻ = in⁻ Γ′ (sel-∅ Γ′)
      σ′ = dhom-base-sub Γ′
      ih = dhom-base-sub-left Γ′
      prf : wkTy A ≡ (A [ ρ⁻ ]T) [ wkSub {A = A} σ′ ]T
      prf = trans (wkTy-sub {A = A} A)
            (trans (cong (λ ρ → A [ ρ ]T)
              (trans (sym (∘-idS-l (wk {Γ = Γ′} {A = A})))
              (trans (cong (λ υ → υ ∘ wk {Γ = Γ′} {A = A}) (sym ih))
              (trans (sym (∘-assoc ρ⁻ σ′ (wk {Γ = Γ′} {A = A})))
              (cong (λ υ → ρ⁻ ∘ υ) (sym (wkSub-∘-r {A = A} σ′)))))))
            (sym ([]T-∘ {A = A} {τ = ρ⁻} {σ = wkSub {A = A} σ′})))
    in
    ⟨ wkSub {A = A} σ′ , vz ⟩:[
      Raw.computed-hasTySub
        (hasTy-conv
          {t = vz {A = A}}
          {A = wkTy A}
          {B = (A [ ρ⁻ ]T) [ wkSub {A = A} σ′ ]T}
          (vz-hasTy {A = A})
          prf) ]

  dhom-base-sub-left : (Γ : Ctx) →
    in⁻ Γ (sel-∅ Γ) ∘ dhom-base-sub Γ ≡ idS Γ
  dhom-base-sub-left Γ with ctx-view Γ
  ... | ◆-view = refl
  ... | ▸-view {Γ = Γ′} A =
    let
      ρ⁻ = in⁻ Γ′ (sel-∅ Γ′)
      σ′ = dhom-base-sub Γ′
      ih = dhom-base-sub-left Γ′
    in
    Sub-ext
      (cong₂ Raw.⟨_,_⟩
        (trans
          (Raw.wkSub-∘ (Raw-Sub ρ⁻) (Raw.wkSub (Raw-Sub σ′)) (Raw.var Raw.zero))
          (trans
            (sym (Raw.wkSub-∘-r (Raw-Sub ρ⁻) (Raw-Sub σ′)))
            (cong Raw.wkSub (cong Raw-Sub ih))))
        refl)

  dhom-base-sub-right : (Γ : Ctx) →
    in⁺ Γ (sel-∅ Γ) ∘ dhom-base-sub Γ ≡ idS Γ
  dhom-base-sub-right Γ with ctx-view Γ
  ... | ◆-view = refl
  ... | ▸-view {Γ = Γ′} A =
    let
      ρ⁺ = in⁺ Γ′ (sel-∅ Γ′)
      σ′ = dhom-base-sub Γ′
      ih = dhom-base-sub-right Γ′
    in
    Sub-ext
      (cong₂ Raw.⟨_,_⟩
        (trans
          (Raw.wkSub-∘ (Raw-Sub ρ⁺) (Raw.wkSub (Raw-Sub σ′)) (Raw.var Raw.zero))
          (trans
            (sym (Raw.wkSub-∘-r (Raw-Sub ρ⁺) (Raw-Sub σ′)))
            (cong Raw.wkSub (cong Raw-Sub ih))))
        refl)
```

## The relative construction

The whole construction is one mutual block. It builds, by recursion on the two
sections:

- `dhom-over` — the diagram-hom telescope, and `dhom-over-B` — one new component;
- `dhom-over-is-DHomOver` / `dhom-step-over` — the `DHomOver` witness;
- `dhom-over-sub` — the **comparison substitution** from the diagram-hom context
  `(Γ ▸▸ D) ▸▸ dhom-over d₁ d₂` into the plain suspended context
  `↑ctx (Γ ▸▸ E) (dty-sel E)`, sending the suspended block via the prefix comparison
  and the two endpoint variables to the (weakened) endpoint terms;
- `dhom-over-sub-left` / `dhom-over-sub-right` — its endpoint laws, identifying its
  composite with `in⁻` / `in⁺` with the two section substitutions;
- `dhom-over-sub-ext` — the **extended** comparison substitution into
  `↑ctx-ext (dty-sel E) A`, obtained from `dhom-over-sub` by `↑sec-ext` across the two
  endpoint terms. This is the genuine computed `Sub` stored in the `ext` field of every
  `DHomStepTyOver`; the previous opaque postulate is gone.

The endpoint laws are what type the two endpoint terms of `↑sec-ext`: a weakened
endpoint `dwkTm-fun H aᵢ` has type `A′ᵢ` reindexed along `dty-proj H`, while
`↑sec-ext` needs it at `A [ in∓ ]T` reindexed along `dhom-over-sub`; the two agree by
the endpoint law plus the diagram-substitution soundness of `A`.

```agda
mutual
  {-# TERMINATING #-}
  dhom-over :
    {Γ : Ctx} {D E : DTy Γ} (d₁ d₂ : DTmOverDTy D E) → DTy (Γ ▸▸ D)
  dhom-over ◆ᴰ ◆ᴰ = ◆ᵈ
  dhom-over {E = E₀ ▸ᵈ A} (d₁ ▸ᴰ a₁ [ p₁ ][ q₁ ]) (d₂ ▸ᴰ a₂ [ p₂ ][ q₂ ]) =
    dhom-over d₁ d₂ ▸ᵈ dhom-over-B {E₀ = E₀} d₁ d₂ A a₁ a₂ p₁ q₁ p₂ q₂

  -- one new hom component, built concretely as A↑ reindexed along the comparison substitution
  dhom-over-B :
    {Γ : Ctx} {D E₀ : DTy Γ} (d₁ d₂ : DTmOverDTy D E₀)
    (A : Ty (Γ ▸▸ E₀))
    {A′₁ A′₂ : Ty (Γ ▸▸ D)} (a₁ a₂ : Tm (Γ ▸▸ D))
    (p₁ : DSubstTyOver d₁ A A′₁) (q₁ : HasTy a₁ A′₁)
    (p₂ : DSubstTyOver d₂ A A′₂) (q₂ : HasTy a₂ A′₂) →
    Ty ((Γ ▸▸ D) ▸▸ dhom-over d₁ d₂)
  dhom-over-B {E₀ = E₀} d₁ d₂ A a₁ a₂ p₁ q₁ p₂ q₂ =
    ↑ty (dty-sel E₀) A [ dhom-over-sub-ext d₁ d₂ A a₁ a₂ p₁ q₁ p₂ q₂ ]T

  dhom-over-is-DHomOver :
    {Γ : Ctx} {D E : DTy Γ} (d₁ d₂ : DTmOverDTy D E) →
    DHomOver d₁ d₂ (dhom-over d₁ d₂)
  dhom-over-is-DHomOver ◆ᴰ ◆ᴰ = dhomover-◆
  dhom-over-is-DHomOver {E = E₀ ▸ᵈ A} (d₁ ▸ᴰ a₁ [ p₁ ][ q₁ ]) (d₂ ▸ᴰ a₂ [ p₂ ][ q₂ ]) =
    dhomover-▸ {B = dhom-over-B {E₀ = E₀} d₁ d₂ A a₁ a₂ p₁ q₁ p₂ q₂}
      (dhom-over-is-DHomOver d₁ d₂)
      (dhom-step-over {E₀ = E₀} d₁ d₂ A a₁ a₂ p₁ q₁ p₂ q₂)

  dhom-step-over :
    {Γ : Ctx} {D E₀ : DTy Γ} (d₁ d₂ : DTmOverDTy D E₀)
    (A : Ty (Γ ▸▸ E₀))
    {A′₁ A′₂ : Ty (Γ ▸▸ D)} (a₁ a₂ : Tm (Γ ▸▸ D))
    (p₁ : DSubstTyOver d₁ A A′₁) (q₁ : HasTy a₁ A′₁)
    (p₂ : DSubstTyOver d₂ A A′₂) (q₂ : HasTy a₂ A′₂) →
    DHomStepTyOver (dhom-over-is-DHomOver d₁ d₂) A a₁ a₂
      (dhom-over-B d₁ d₂ A a₁ a₂ p₁ q₁ p₂ q₂)
  dhom-step-over {E₀ = E₀} d₁ d₂ A a₁ a₂ p₁ q₁ p₂ q₂ =
    record
      { nctx    = ↑ctx-NatCtx (_ ▸▸ E₀) (dty-sel E₀)
      ; next    = ↑ctx-ext-NatCtxExt (dty-sel E₀) A
      ; nty     = ↑ty-NatTy (dty-sel E₀) A
      ; wk₁     = dwkTm-rel (dhom-over d₁ d₂) a₁
      ; wk₂     = dwkTm-rel (dhom-over d₁ d₂) a₂
      ; ext     = dhom-over-sub-ext d₁ d₂ A a₁ a₂ p₁ q₁ p₂ q₂
      ; reindex = Raw.substTy (Raw-Ty (↑ty (dty-sel E₀) A))
                    (Raw-Sub (dhom-over-sub-ext d₁ d₂ A a₁ a₂ p₁ q₁ p₂ q₂))
      }

  -- The comparison substitution into the plain suspended context.
  dhom-over-sub :
    {Γ : Ctx} {D E : DTy Γ} (d₁ d₂ : DTmOverDTy D E) →
    Sub ((Γ ▸▸ D) ▸▸ dhom-over d₁ d₂) (↑ctx (Γ ▸▸ E) (dty-sel E))
  dhom-over-sub {Γ} {D} ◆ᴰ ◆ᴰ = dhom-base-sub Γ ∘ dty-proj D
  dhom-over-sub {E = E₀ ▸ᵈ A} (d₁ ▸ᴰ a₁ [ p₁ ][ q₁ ]) (d₂ ▸ᴰ a₂ [ p₂ ][ q₂ ]) =
    let ends = dhom-over-sub-ext d₁ d₂ A a₁ a₂ p₁ q₁ p₂ q₂
    in ⟨ wkSub {A = ↑ty (dty-sel E₀) A [ ends ]T} ends , vz {A = ↑ty (dty-sel E₀) A [ ends ]T} ⟩:[
         vz-wkSub-hasTySub {A = ↑ty (dty-sel E₀) A} ends ]

  -- The extended comparison substitution: ↑sec-ext applied to dhom-over-sub.
  -- Defined before the endpoint laws so that its clauses are available for
  -- reduction inside the (later) law proofs (`ends` must unfold to a snoc there).
  dhom-over-sub-ext :
    {Γ : Ctx} {D E₀ : DTy Γ} (d₁ d₂ : DTmOverDTy D E₀)
    (A : Ty (Γ ▸▸ E₀))
    {A′₁ A′₂ : Ty (Γ ▸▸ D)} (a₁ a₂ : Tm (Γ ▸▸ D))
    (p₁ : DSubstTyOver d₁ A A′₁) (q₁ : HasTy a₁ A′₁)
    (p₂ : DSubstTyOver d₂ A A′₂) (q₂ : HasTy a₂ A′₂) →
    Sub ((Γ ▸▸ D) ▸▸ dhom-over d₁ d₂) (↑ctx-ext (dty-sel E₀) A)
  dhom-over-sub-ext {Γ} {D} {E₀} d₁ d₂ A {A′₁} {A′₂} a₁ a₂ p₁ q₁ p₂ q₂ =
    ↑sec-ext (dty-sel E₀) A
      (dhom-over-sub d₁ d₂)
      (dwkTm-fun H a₁) (dwkTm-fun H a₂)
      {A⁻ = A [ in⁻ (Γ ▸▸ E₀) (dty-sel E₀) ]T}
      {A⁺ = A [ in⁺ (Γ ▸▸ E₀) (dty-sel E₀) ]T}
      (Raw.substTy (Raw-Ty A) (Raw-Sub (in⁻ (Γ ▸▸ E₀) (dty-sel E₀))))
      (Raw.substTy (Raw-Ty A) (Raw-Sub (in⁺ (Γ ▸▸ E₀) (dty-sel E₀))))
      p⁻ p⁺
    where
      H : DTy (Γ ▸▸ D)
      H = dhom-over d₁ d₂

      ρ⁻ = in⁻ (Γ ▸▸ E₀) (dty-sel E₀)
      ρ⁺ = in⁺ (Γ ▸▸ E₀) (dty-sel E₀)

      e⁻ : (A [ ρ⁻ ]T) [ dhom-over-sub d₁ d₂ ]T ≡ A′₁ [ dty-proj H ]T
      e⁻ =
        trans ([]T-∘ {A = A} {τ = ρ⁻} {σ = dhom-over-sub d₁ d₂})
        (trans (cong (λ ρ → A [ ρ ]T) (dhom-over-sub-left d₁ d₂))
        (trans (sym ([]T-∘ {A = A} {τ = dover-sub d₁} {σ = dty-proj H}))
               (cong (λ C → C [ dty-proj H ]T) (Ty-ext (dsubstTyOver-sound-raw d₁ p₁)))))

      e⁺ : (A [ ρ⁺ ]T) [ dhom-over-sub d₁ d₂ ]T ≡ A′₂ [ dty-proj H ]T
      e⁺ =
        trans ([]T-∘ {A = A} {τ = ρ⁺} {σ = dhom-over-sub d₁ d₂})
        (trans (cong (λ ρ → A [ ρ ]T) (dhom-over-sub-right d₁ d₂))
        (trans (sym ([]T-∘ {A = A} {τ = dover-sub d₂} {σ = dty-proj H}))
               (cong (λ C → C [ dty-proj H ]T) (Ty-ext (dsubstTyOver-sound-raw d₂ p₂)))))

      p⁻ : HasTySub (dwkTm-fun H a₁) (A [ ρ⁻ ]T) (dhom-over-sub d₁ d₂)
      p⁻ = hasTySub-conv
             {t = dwkTm-fun H a₁} {A = A′₁} {B = A [ ρ⁻ ]T}
             {σ = dty-proj H} {τ = dhom-over-sub d₁ d₂}
             (dwkTm-hasTySub H {t = a₁} {A = A′₁} q₁)
             (sym e⁻)

      p⁺ : HasTySub (dwkTm-fun H a₂) (A [ ρ⁺ ]T) (dhom-over-sub d₁ d₂)
      p⁺ = hasTySub-conv
             {t = dwkTm-fun H a₂} {A = A′₂} {B = A [ ρ⁺ ]T}
             {σ = dty-proj H} {τ = dhom-over-sub d₁ d₂}
             (dwkTm-hasTySub H {t = a₂} {A = A′₂} q₂)
             (sym e⁺)

  -- Endpoint laws of the comparison substitution.
  dhom-over-sub-left :
    {Γ : Ctx} {D E : DTy Γ} (d₁ d₂ : DTmOverDTy D E) →
    in⁻ (Γ ▸▸ E) (dty-sel E) ∘ dhom-over-sub d₁ d₂
      ≡ dover-sub d₁ ∘ dty-proj (dhom-over d₁ d₂)
  dhom-over-sub-left {Γ} {D} ◆ᴰ ◆ᴰ =
    trans (∘-assoc (in⁻ Γ (sel-∅ Γ)) (dhom-base-sub Γ) (dty-proj D))
      (trans (cong (λ τ → τ ∘ dty-proj D) (dhom-base-sub-left Γ))
        (trans (∘-idS-l (dty-proj D))
          (sym (∘-idS-r (dty-proj D)))))
  dhom-over-sub-left {Γ} {D} {E = E₀ ▸ᵈ A}
    (d₁ ▸ᴰ a₁ [ p₁ ][ q₁ ]) (d₂ ▸ᴰ a₂ [ p₂ ][ q₂ ]) =
    let
      H₀   = dhom-over d₁ d₂
      proj = dty-proj H₀
      s    = dhom-over-sub d₁ d₂
      ρ⁻   = in⁻ (Γ ▸▸ E₀) (dty-sel E₀)
      ends = dhom-over-sub-ext d₁ d₂ A a₁ a₂ p₁ q₁ p₂ q₂
      B    = ↑ty (dty-sel E₀) A [ ends ]T
      sρ⁻  = Raw-Sub ρ⁻
      ssub = Raw-Sub s
      e1   = Raw-Sub (dover-sub d₁)
      e2   = Raw-Sub proj
      endR = Raw-Sub ends
      first =
        trans (Raw.wkSub-∘ (Raw.wkSub (Raw.wkSub sρ⁻)) (Raw.wkSub endR) (Raw.var Raw.zero))
        (trans (sym (Raw.wkSub-∘-r (Raw.wkSub (Raw.wkSub sρ⁻)) endR))
        (trans (cong Raw.wkSub (Raw.wkSub-∘ (Raw.wkSub sρ⁻) (Raw.⟨ ssub , Raw-Tm (dwkTm-fun H₀ a₁) ⟩) (Raw-Tm (dwkTm-fun H₀ a₂))))
        (trans (cong Raw.wkSub (Raw.wkSub-∘ sρ⁻ ssub (Raw-Tm (dwkTm-fun H₀ a₁))))
        (trans (cong Raw.wkSub (cong Raw-Sub (dhom-over-sub-left d₁ d₂)))
        (trans (Raw.wkSub-∘-r {A = Raw-Ty B} e1 e2)
               (cong (λ z → e1 Raw.∘ z) (cong Raw-Sub (wkSub-∘-r {A = B} proj))))))))
      second =
        trans (cong Raw.wkTm (cong Raw-Tm (dwkTm-fun-proj H₀ a₁)))
        (trans (Raw.wkTm-[]t-r (Raw-Tm a₁) e2)
               (cong (λ z → Raw-Tm a₁ Raw.[ z ]t) (cong Raw-Sub (wkSub-∘-r {A = B} proj))))
    in
    Sub-ext (cong₂ Raw.⟨_,_⟩ first second)

  dhom-over-sub-right :
    {Γ : Ctx} {D E : DTy Γ} (d₁ d₂ : DTmOverDTy D E) →
    in⁺ (Γ ▸▸ E) (dty-sel E) ∘ dhom-over-sub d₁ d₂
      ≡ dover-sub d₂ ∘ dty-proj (dhom-over d₁ d₂)
  dhom-over-sub-right {Γ} {D} ◆ᴰ ◆ᴰ =
    trans (∘-assoc (in⁺ Γ (sel-∅ Γ)) (dhom-base-sub Γ) (dty-proj D))
      (trans (cong (λ τ → τ ∘ dty-proj D) (dhom-base-sub-right Γ))
        (trans (∘-idS-l (dty-proj D))
          (sym (∘-idS-r (dty-proj D)))))
  dhom-over-sub-right {Γ} {D} {E = E₀ ▸ᵈ A}
    (d₁ ▸ᴰ a₁ [ p₁ ][ q₁ ]) (d₂ ▸ᴰ a₂ [ p₂ ][ q₂ ]) =
    let
      H₀   = dhom-over d₁ d₂
      proj = dty-proj H₀
      s    = dhom-over-sub d₁ d₂
      ρ⁺   = in⁺ (Γ ▸▸ E₀) (dty-sel E₀)
      ends = dhom-over-sub-ext d₁ d₂ A a₁ a₂ p₁ q₁ p₂ q₂
      B    = ↑ty (dty-sel E₀) A [ ends ]T
      sρ⁺  = Raw-Sub ρ⁺
      ssub = Raw-Sub s
      e1   = Raw-Sub (dover-sub d₂)
      e2   = Raw-Sub proj
      endR = Raw-Sub ends
      first =
        trans (Raw.wkSub-∘ (Raw.wkSub (Raw.wkSub sρ⁺)) (Raw.wkSub endR) (Raw.var Raw.zero))
        (trans (sym (Raw.wkSub-∘-r (Raw.wkSub (Raw.wkSub sρ⁺)) endR))
        (trans (cong Raw.wkSub (Raw.wkSub-∘ (Raw.wkSub sρ⁺) (Raw.⟨ ssub , Raw-Tm (dwkTm-fun H₀ a₁) ⟩) (Raw-Tm (dwkTm-fun H₀ a₂))))
        (trans (cong Raw.wkSub (Raw.wkSub-∘ sρ⁺ ssub (Raw-Tm (dwkTm-fun H₀ a₁))))
        (trans (cong Raw.wkSub (cong Raw-Sub (dhom-over-sub-right d₁ d₂)))
        (trans (Raw.wkSub-∘-r {A = Raw-Ty B} e1 e2)
               (cong (λ z → e1 Raw.∘ z) (cong Raw-Sub (wkSub-∘-r {A = B} proj))))))))
      second =
        trans (cong Raw.wkTm (cong Raw-Tm (dwkTm-fun-proj H₀ a₂)))
        (trans (Raw.wkTm-[]t-r (Raw-Tm a₂) e2)
               (cong (λ z → Raw-Tm a₂ Raw.[ z ]t) (cong Raw-Sub (wkSub-∘-r {A = B} proj))))
    in
    Sub-ext (cong₂ Raw.⟨_,_⟩ first second)
```

## Ordinary chosen hom (empty source)

The ordinary chosen hom of two diagram terms is the relative chosen hom over the empty
source diagram. Because `Γ ▸▸ ◆ᵈ` reduces to `Γ`, the carrier is `DTy Γ` and the
witness `dhom-is-DHom` is `dhom-over-is-DHomOver` read at `◆ᵈ` — no transport.

```agda
dhom :
  {Γ : Ctx} {E : DTy Γ} →
  DTm E → DTm E → DTy Γ
dhom d₁ d₂ = dhom-over (toOver d₁) (toOver d₂)

dhom-is-DHom :
  {Γ : Ctx} {E : DTy Γ} →
  (d₁ d₂ : DTm E) →
  DHom d₁ d₂ (dhom d₁ d₂)
dhom-is-DHom d₁ d₂ = dhom-over-is-DHomOver (toOver d₁) (toOver d₂)
```
