# 4e-DiagramEquivalences: Equivalences Of Diagram Types

We now define when a morphism of diagram types is an equivalences.

```agda
module 4e-DiagramEquivalences where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import 4d-DiagramMorphisms as DM

open DM public
open import 4c-LaxAlgebra using (dhom-comp)

eq-lax :
  {Γ : Ctx} {D E : DTy Γ} →
  {φ ψ : D ⇝ E} →
  φ ≡ ψ →
  LaxTransformation φ ψ
eq-lax refl = id⇒ _

vert-lax :
  {Γ : Ctx} {D E : DTy Γ} →
  {φ ψ χ : D ⇝ E} →
  LaxTransformation ψ χ →
  LaxTransformation φ ψ →
  LaxTransformation φ χ
vert-lax = _∘⇒_

inv-lax :
  {Γ : Ctx} {D E : DTy Γ} →
  {φ ψ : D ⇝ E} →
  LaxTransformation φ ψ →
  LaxTransformation ψ φ
inv-lax = lax-inv

id-left-lax :
  {Γ : Ctx} {D E : DTy Γ} →
  (φ : D ⇝ E) →
  LaxTransformation (id⇝ E ∘⇝ φ) φ
id-left-lax φ = eq-lax (lunit⇝ φ)

id-right-lax :
  {Γ : Ctx} {D E : DTy Γ} →
  (φ : D ⇝ E) →
  LaxTransformation (φ ∘⇝ id⇝ D) φ
id-right-lax φ = eq-lax (runit⇝ φ)

assoc-lax :
  {Γ : Ctx} {D E F G : DTy Γ} →
  (χ : F ⇝ G) →
  (ψ : E ⇝ F) →
  (φ : D ⇝ E) →
  LaxTransformation ((χ ∘⇝ ψ) ∘⇝ φ) (χ ∘⇝ (ψ ∘⇝ φ))
assoc-lax χ ψ φ = eq-lax (assoc⇝ φ ψ χ)

lwhisk-lax :
  {Γ : Ctx} {D E F : DTy Γ} →
  (χ : E ⇝ F) →
  {φ ψ : D ⇝ E} →
  LaxTransformation φ ψ →
  LaxTransformation (χ ∘⇝ φ) (χ ∘⇝ ψ)
lwhisk-lax χ α = lax-rwhisk α χ

rwhisk-lax :
  {Γ : Ctx} {D E F : DTy Γ} →
  {ψ χ : E ⇝ F} →
  LaxTransformation ψ χ →
  (φ : D ⇝ E) →
  LaxTransformation (ψ ∘⇝ φ) (χ ∘⇝ φ)
rwhisk-lax α φ = lax-lwhisk φ α
```

## Diagram Equivalences

```agda
record DiagramEquiv
  {Γ : Ctx}
  {σ τ : DTy Γ}
  (to : σ ⇝ τ)
  : Set₁
  where
  constructor mkDiagramEquiv
  field
    from    : τ ⇝ σ
    unit    : LaxTransformation (id⇝ σ) (from ∘⇝ to)
    counit  : LaxTransformation (id⇝ τ) (to ∘⇝ from)

open DiagramEquiv public using (from; unit; counit)

abstract
  diagram-equiv-counit-hom :
    {Γ : Ctx}
    {σ τ : DTy Γ}
    {φ : σ ⇝ τ} →
    (e : DiagramEquiv φ) →
    (d : DTm τ) →
    DTm
      (dhom
        d
        (apply-diag-mor φ
          (apply-diag-mor (from e) d)))
  diagram-equiv-counit-hom {φ = φ} e d =
    dhom-comp
      (apply-diag-mor-comp-hom (from e) φ d)
      (dhom-comp
        (apply-lax-transformation (counit e) d)
        (apply-id-diag-mor-hom d))

  diagram-equiv-unit-hom :
    {Γ : Ctx}
    {σ τ : DTy Γ}
    {φ : σ ⇝ τ} →
    (e : DiagramEquiv φ) →
    (s : DTm σ) →
    DTm
      (dhom
        s
        (apply-diag-mor (from e)
          (apply-diag-mor φ s)))
  diagram-equiv-unit-hom {φ = φ} e s =
    dhom-comp
      (apply-diag-mor-comp-hom φ (from e) s)
      (dhom-comp
        (apply-lax-transformation (unit e) s)
        (apply-id-diag-mor-hom s))

  diagram-equiv-counit-hom-to :
    {Γ : Ctx}
    {σ τ : DTy Γ}
    {φ : σ ⇝ τ} →
    (e : DiagramEquiv φ) →
    (d : DTm τ) →
    {z : DTm τ} →
    DTm (dhom (apply-diag-mor φ (apply-diag-mor (from e) d)) z) →
    DTm (dhom d z)
  diagram-equiv-counit-hom-to e d hz =
    dhom-comp hz (diagram-equiv-counit-hom e d)

  diagram-equiv-unit-hom-to :
    {Γ : Ctx}
    {σ τ : DTy Γ}
    {φ : σ ⇝ τ} →
    (e : DiagramEquiv φ) →
    (s : DTm σ) →
    {z : DTm τ} →
    DTm (dhom (apply-diag-mor φ s) z) →
    DTm (dhom s (apply-diag-mor (from e) z))
  diagram-equiv-unit-hom-to {φ = φ} e s hz =
    dhom-comp
      (apply-diag-mor-hom (from e) hz)
      (diagram-equiv-unit-hom e s)

record DEquiv
  {Γ : Ctx}
  (D E : DTy Γ)
  : Set₁
  where
  constructor mkDEquiv
  field
    map : D ⇝ E
    is-equiv : DiagramEquiv map

open DEquiv public
```

## Proposition 4.13

```agda
module Properties where

  diagram-equiv-id :
    {Γ : Ctx}
    (σ : DTy Γ) →
    DiagramEquiv (id⇝ σ)
  diagram-equiv-id σ = record
    { from = id⇝ σ
    ; unit = inv-lax (id-right-lax (id⇝ σ))
    ; counit = inv-lax (id-right-lax (id⇝ σ))
    }

  diagram-equiv-inv :
    {Γ : Ctx}
    {σ τ : DTy Γ} →
    {φ : σ ⇝ τ} →
    (e : DiagramEquiv φ) →
    DiagramEquiv (from e)
  diagram-equiv-inv {φ = φ} e = record
    { from = φ
    ; unit = counit e
    ; counit = unit e
    }

  diagram-equiv-comp :
    {Γ : Ctx}
    {σ τ υ : DTy Γ} →
    {φ : σ ⇝ τ} →
    {ψ : τ ⇝ υ} →
    DiagramEquiv φ →
    DiagramEquiv ψ →
    DiagramEquiv (ψ ∘⇝ φ)
  diagram-equiv-comp
    {σ = σ} {τ = τ} {υ = υ}
    {φ = φ} {ψ = ψ}
    eφ eψ = record
    { from = from eφ ∘⇝ from eψ
    ; unit = assoc-final
    ; counit = assoc-final'
    }
    where
      unit-step₁ :
        LaxTransformation (from eφ ∘⇝ φ) (from eφ ∘⇝ (id⇝ τ ∘⇝ φ))
      unit-step₁ =
        inv-lax
          (lwhisk-lax (from eφ) (id-left-lax φ))

      unit-step₂ :
        LaxTransformation
          (from eφ ∘⇝ (id⇝ τ ∘⇝ φ))
          (from eφ ∘⇝ ((from eψ ∘⇝ ψ) ∘⇝ φ))
      unit-step₂ = lwhisk-lax (from eφ) (rwhisk-lax (unit eψ) φ)

      unit-step₃ :
        LaxTransformation
          (from eφ ∘⇝ ((from eψ ∘⇝ ψ) ∘⇝ φ))
          (from eφ ∘⇝ (from eψ ∘⇝ (ψ ∘⇝ φ)))
      unit-step₃ =
        lwhisk-lax (from eφ) (assoc-lax (from eψ) ψ φ)

      unit-step₄ :
        LaxTransformation
          (from eφ ∘⇝ (from eψ ∘⇝ (ψ ∘⇝ φ)))
          ((from eφ ∘⇝ from eψ) ∘⇝ (ψ ∘⇝ φ))
      unit-step₄ = inv-lax (assoc-lax (from eφ) (from eψ) (ψ ∘⇝ φ))

      assoc-final :
        LaxTransformation (id⇝ σ) ((from eφ ∘⇝ from eψ) ∘⇝ (ψ ∘⇝ φ))
      assoc-final =
        vert-lax unit-step₄
          (vert-lax unit-step₃
            (vert-lax unit-step₂
              (vert-lax unit-step₁ (unit eφ))))

      counit-step₁ :
        LaxTransformation (ψ ∘⇝ from eψ) (ψ ∘⇝ (id⇝ τ ∘⇝ from eψ))
      counit-step₁ =
        inv-lax
          (lwhisk-lax ψ (id-left-lax (from eψ)))

      counit-step₂ :
        LaxTransformation
          (ψ ∘⇝ (id⇝ τ ∘⇝ from eψ))
          (ψ ∘⇝ ((φ ∘⇝ from eφ) ∘⇝ from eψ))
      counit-step₂ = lwhisk-lax ψ (rwhisk-lax (counit eφ) (from eψ))

      counit-step₃ :
        LaxTransformation
          (ψ ∘⇝ ((φ ∘⇝ from eφ) ∘⇝ from eψ))
          (ψ ∘⇝ (φ ∘⇝ (from eφ ∘⇝ from eψ)))
      counit-step₃ =
        lwhisk-lax ψ (assoc-lax φ (from eφ) (from eψ))

      counit-step₄ :
        LaxTransformation
          (ψ ∘⇝ (φ ∘⇝ (from eφ ∘⇝ from eψ)))
          ((ψ ∘⇝ φ) ∘⇝ (from eφ ∘⇝ from eψ))
      counit-step₄ = inv-lax (assoc-lax ψ φ (from eφ ∘⇝ from eψ))

      assoc-final' :
        LaxTransformation (id⇝ υ) ((ψ ∘⇝ φ) ∘⇝ (from eφ ∘⇝ from eψ))
      assoc-final' =
        vert-lax counit-step₄
          (vert-lax counit-step₃
            (vert-lax counit-step₂
              (vert-lax counit-step₁ (counit eψ))))

  record LeftInverse
    {Γ : Ctx}
    (σ τ : DTy Γ)
    (φ : σ ⇝ τ)
    : Set₁
    where
    constructor mkLeftInverse
    field
      inv     : τ ⇝ σ
      witness : LaxTransformation (id⇝ σ) (inv ∘⇝ φ)

  record RightInverse
    {Γ : Ctx}
    (σ τ : DTy Γ)
    (φ : σ ⇝ τ)
    : Set₁
    where
    constructor mkRightInverse
    field
      inv     : τ ⇝ σ
      witness : LaxTransformation (id⇝ τ) (φ ∘⇝ inv)

  open LeftInverse public using (inv; witness)
  open RightInverse public using (inv; witness)

  diagram-equiv-left-inverse :
    {Γ : Ctx}
    {σ τ : DTy Γ} →
    {φ : σ ⇝ τ} →
    DiagramEquiv φ →
    LeftInverse σ τ φ
  diagram-equiv-left-inverse e = mkLeftInverse (from e) (unit e)

  diagram-equiv-right-inverse :
    {Γ : Ctx}
    {σ τ : DTy Γ} →
    {φ : σ ⇝ τ} →
    DiagramEquiv φ →
    RightInverse σ τ φ
  diagram-equiv-right-inverse e = mkRightInverse (from e) (counit e)

  left-right-inverses-agree :
    {Γ : Ctx}
    {σ τ : DTy Γ} →
    {φ : σ ⇝ τ} →
    (left : LeftInverse σ τ φ) →
    (right : RightInverse σ τ φ) →
    LaxTransformation (LeftInverse.inv left) (RightInverse.inv right)
  left-right-inverses-agree
    {σ = σ} {τ = τ} {φ = φ}
    left right =
    vert-lax agree-step₅
      (vert-lax agree-step₄
        (vert-lax agree-step₃
          (vert-lax agree-step₂ agree-step₁)))
    where
      agree-step₁ :
        LaxTransformation (inv left) (inv left ∘⇝ id⇝ τ)
      agree-step₁ = inv-lax (id-right-lax (inv left))

      agree-step₂ :
        LaxTransformation
          (inv left ∘⇝ id⇝ τ)
          (inv left ∘⇝ (φ ∘⇝ inv right))
      agree-step₂ = inv-lax (lwhisk-lax (inv left) (inv-lax (witness right)))

      agree-step₃ :
        LaxTransformation
          (inv left ∘⇝ (φ ∘⇝ inv right))
          ((inv left ∘⇝ φ) ∘⇝ inv right)
      agree-step₃ = inv-lax (assoc-lax (inv left) φ (inv right))

      agree-step₄ :
        LaxTransformation
          ((inv left ∘⇝ φ) ∘⇝ inv right)
          ((id⇝ σ) ∘⇝ inv right)
      agree-step₄ = rwhisk-lax (inv-lax (witness left)) (inv right)

      agree-step₅ :
        LaxTransformation ((id⇝ σ) ∘⇝ inv right) (inv right)
      agree-step₅ = id-left-lax (inv right)

  left-right-inverses→equiv :
    {Γ : Ctx}
    {σ τ : DTy Γ} →
    {φ : σ ⇝ τ} →
    LeftInverse σ τ φ →
    RightInverse σ τ φ →
    DiagramEquiv φ
  left-right-inverses→equiv {φ = φ} left right = record
    { from = inv left
    ; unit = witness left
    ; counit = vert-lax
        (inv-lax (lwhisk-lax φ agree))
        (witness right)
    }
    where
      agree :
        LaxTransformation (inv left) (inv right)
      agree = left-right-inverses-agree left right

  record DiagramMorIso
    {Γ : Ctx}
    {σ τ : DTy Γ}
    (φ ψ : σ ⇝ τ)
    : Set₁
    where
    constructor mkDiagramMorIso
    field
      to-lax   : LaxTransformation φ ψ
      from-lax : LaxTransformation ψ φ

  diagram-mor-iso-preserves-equiv :
    {Γ : Ctx}
    {σ τ : DTy Γ} →
    {φ ψ : σ ⇝ τ} →
    DiagramMorIso φ ψ →
    DiagramEquiv ψ →
    DiagramEquiv φ
  diagram-mor-iso-preserves-equiv {φ = φ} {ψ = ψ} i e = record
    { from = from e
    ; unit = vert-lax (lwhisk-lax (from e) (DiagramMorIso.from-lax i)) (unit e)
    ; counit = vert-lax
        (inv-lax (rwhisk-lax (DiagramMorIso.to-lax i) (from e)))
        (counit e)
    }

  equiv-2-out-of-3-right :
    {Γ : Ctx}
    {σ τ υ : DTy Γ} →
    {φ : σ ⇝ τ} →
    {ψ : τ ⇝ υ} →
    DiagramEquiv ψ →
    DiagramEquiv (ψ ∘⇝ φ) →
    DiagramEquiv φ
  equiv-2-out-of-3-right
    {σ = σ} {τ = τ} {υ = υ}
    {φ = φ} {ψ = ψ}
    eψ eψφ =
    diagram-mor-iso-preserves-equiv iso
      (diagram-equiv-comp eψφ (diagram-equiv-inv eψ))
    where
      iso-to :
        LaxTransformation φ (from eψ ∘⇝ (ψ ∘⇝ φ))
      iso-to =
        vert-lax
          (assoc-lax (from eψ) ψ φ)
          (vert-lax
            (rwhisk-lax (unit eψ) φ)
            (inv-lax (id-left-lax φ)))

      iso-from :
        LaxTransformation (from eψ ∘⇝ (ψ ∘⇝ φ)) φ
      iso-from =
        vert-lax
          (id-left-lax φ)
          (vert-lax
            (rwhisk-lax (inv-lax (unit eψ)) φ)
            (inv-lax (assoc-lax (from eψ) ψ φ)))

      iso : DiagramMorIso φ (from eψ ∘⇝ (ψ ∘⇝ φ))
      iso = mkDiagramMorIso iso-to iso-from

  equiv-2-out-of-3-middle :
    {Γ : Ctx}
    {σ τ υ : DTy Γ} →
    {φ : σ ⇝ τ} →
    {ψ : τ ⇝ υ} →
    DiagramEquiv φ →
    DiagramEquiv (ψ ∘⇝ φ) →
    DiagramEquiv ψ
  equiv-2-out-of-3-middle
    {σ = σ} {τ = τ} {υ = υ}
    {φ = φ} {ψ = ψ}
    eφ eψφ =
    diagram-mor-iso-preserves-equiv iso
      (diagram-equiv-comp (diagram-equiv-inv eφ) eψφ)
    where
      iso-to :
        LaxTransformation ψ ((ψ ∘⇝ φ) ∘⇝ from eφ)
      iso-to =
        vert-lax
          (inv-lax (assoc-lax ψ φ (from eφ)))
          (vert-lax
            (lwhisk-lax ψ (counit eφ))
            (inv-lax (id-right-lax ψ)))

      iso-from :
        LaxTransformation ((ψ ∘⇝ φ) ∘⇝ from eφ) ψ
      iso-from =
        vert-lax
          (id-right-lax ψ)
          (vert-lax
            (lwhisk-lax ψ (inv-lax (counit eφ)))
            (assoc-lax ψ φ (from eφ)))

      iso : DiagramMorIso ψ ((ψ ∘⇝ φ) ∘⇝ from eφ)
      iso = mkDiagramMorIso iso-to iso-from

  record TwoOutOfSix
    {Γ : Ctx}
    {σ τ υ ω : DTy Γ}
    (φ : σ ⇝ τ)
    (ψ : τ ⇝ υ)
    (ξ : υ ⇝ ω)
    : Set₁
    where
    constructor mkTwoOutOfSix
    field
      φ-equiv : DiagramEquiv φ
      ψ-equiv : DiagramEquiv ψ
      ξ-equiv : DiagramEquiv ξ

  equiv-2-out-of-6 :
    {Γ : Ctx}
    {σ τ υ ω : DTy Γ} →
    {φ : σ ⇝ τ} →
    {ψ : τ ⇝ υ} →
    {ξ : υ ⇝ ω} →
    DiagramEquiv (ψ ∘⇝ φ) →
    DiagramEquiv (ξ ∘⇝ ψ) →
    TwoOutOfSix φ ψ ξ
  equiv-2-out-of-6
    {σ = σ} {τ = τ} {υ = υ} {ω = ω}
    {φ = φ} {ψ = ψ} {ξ = ξ}
    eψφ eξψ =
    mkTwoOutOfSix φ-equiv ψ-equiv ξ-equiv
    where
      ψ-left :
        LeftInverse τ υ ψ
      ψ-left = mkLeftInverse
        (from eξψ ∘⇝ ξ)
        (vert-lax
          (inv-lax (assoc-lax (from eξψ) ξ ψ))
          (unit eξψ))

      ψ-right :
        RightInverse τ υ ψ
      ψ-right = mkRightInverse
        (φ ∘⇝ from eψφ)
        (vert-lax
          (assoc-lax ψ φ (from eψφ))
          (counit eψφ))

      ψ-equiv : DiagramEquiv ψ
      ψ-equiv = left-right-inverses→equiv ψ-left ψ-right

      φ-equiv : DiagramEquiv φ
      φ-equiv = equiv-2-out-of-3-right ψ-equiv eψφ

      ξ-equiv : DiagramEquiv ξ
      ξ-equiv = equiv-2-out-of-3-middle ψ-equiv eξψ
```
