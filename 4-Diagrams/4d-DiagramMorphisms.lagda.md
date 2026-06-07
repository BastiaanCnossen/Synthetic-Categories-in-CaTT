# 4d-DiagramMorphisms: diagram morphisms and lax transformations

A morphism `D ⇝ E` of diagram types is a section of the target diagram `E` over the
total context of the source diagram `D`. In the notation of `4a-Diagrams`, this is
precisely a term `DTmOverDTy D E`: a *relative section*. This representation avoids
naming a projection substitution `Γ ▸▸ D → Γ`; the action of a morphism on types, terms,
substitutions, and variables is the computed action layer of `4a-Diagrams-Comp`
(`dsubstTyOver-fun`, `dsubstTmOver-fun`, …), built from the underlying substitution
`dover-sub`.

The file develops:

- **Identity and composition** of morphisms, as chosen constructions. Earlier drafts
  recognized them through exported structural relations `IdOver` / `CompOver`; those are
  gone. `id⇝` is the identity relative section `id-over`, and `_∘⇝_` re-bases the second
  section through the first via `comp-over`. Both are genuine definitions built on the
  action layer.
- **Lax transformations**: a lax transformation between two morphisms `φ , ψ : D ⇝ E`
  is a term of the relative diagram hom `dhom-over (map φ) (map ψ)` — the diagram hom
  over the source `D` between the two sections. This is why `4b-DiagramHoms` takes the
  relative `DHomOver` as primary.
- **The evaluation API** used by the equivalence files (`4e`): applying a morphism to a
  point of the source diagram, and transporting diagram-hom terms along morphisms and
  lax transformations.

This file is self-contained: it imports the action layer from `4a-Diagrams-Comp` and the
chosen relative hom `dhom-over` from `4b-DiagramHoms-Comp`, so there is no separate
`-Comp` companion.

```agda
module 4d-DiagramMorphisms where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import 2a-CaTT public
open import 4a-Diagrams-Comp public
open import 4b-DiagramHoms-Comp public
```

## Morphisms

A morphism `D ⇝ E` is a section of `E` over the source diagram context `Γ ▸▸ D`.

```agda
infixr 20 _⇝_

record _⇝_ {Γ : Ctx} (D E : DTy Γ) : Set₁ where
  constructor mk
  field
    map : DTmOverDTy D E
```

```agda
open _⇝_ public using (map)
```

## Identity and composition

The identity morphism is the identity relative section `id-over D` (whose underlying
substitution is `idS`). Composition re-bases the second section through the first with
`comp-over` (whose underlying substitution is the composite `dover-sub ψ ∘ dover-sub φ`).
Both are definitions from the action layer; no structural recognizer is needed.

```agda
id⇝ : {Γ : Ctx} → (D : DTy Γ) → D ⇝ D
id⇝ D = mk (id-over D)
```

```agda
infixr 30 _∘⇝_

_∘⇝_ :
  {Γ : Ctx} {D E F : DTy Γ} →
  E ⇝ F → D ⇝ E → D ⇝ F
ψ ∘⇝ φ = mk (comp-over (map φ) (map ψ))
```

## Lax transformations

A **lax transformation** between two morphisms `φ , ψ : D ⇝ E` is a term of the relative
diagram hom `dhom-over (map φ) (map ψ)`: the diagram hom over the source `D` between the
two sections. This is the relative-hom carrier from `4b-DiagramHoms-Comp`; making it the
carrier is exactly why the relative `DHomOver` is the primary notion.

The lax-transformation record reuses the field name `map` (as the morphism record does).
The two records share the name intentionally; `map φ` resolves to the morphism
projection, and the lax-transformation projection is reached as `LaxTransformation.map`
when needed.

```agda
record LaxTransformation
  {Γ : Ctx}
  {D E : DTy Γ}
  (φ ψ : D ⇝ E)
  : Set₁
  where
  constructor mk
  field
    map : DTm (dhom-over (map φ) (map ψ))
```

```agda
_⇒_ : {Γ : Ctx} {D E : DTy Γ} → (φ ψ : D ⇝ E) → Set₁
φ ⇒ ψ = LaxTransformation φ ψ
```

## Category laws

The unit and associativity laws for `id⇝` / `_∘⇝_`. Their underlying sections agree on
the nose (`id-over` is the `idS` section and `comp-over` composes underlying
substitutions), but proving them as section equalities needs `DTmOverDTy`
extensionality, which is not yet available; they are exposed as chosen laws.

```agda
postulate
  lunit⇝ :
    {Γ : Ctx} {D E : DTy Γ} →
    (φ : D ⇝ E) → id⇝ E ∘⇝ φ ≡ φ

  runit⇝ :
    {Γ : Ctx} {D E : DTy Γ} →
    (φ : D ⇝ E) → φ ∘⇝ id⇝ D ≡ φ

  assoc⇝ :
    {Γ : Ctx} {D E F G : DTy Γ} →
    (φ : D ⇝ E) (ψ : E ⇝ F) (χ : F ⇝ G) →
    (χ ∘⇝ ψ) ∘⇝ φ ≡ χ ∘⇝ (ψ ∘⇝ φ)
```

## Lax-transformation algebra

The identity, vertical composition, inverse, and whiskerings of lax transformations.
A lax transformation is a term of a relative diagram hom `dhom-over (map φ) (map ψ)`, so
these mirror the term-level operations on diagram homs (`4c-LaxAlgebra`) in the relative
setting; they are exposed as chosen operations until the relative analogues of
`dhom-comp` / `dhom-inv` are constructed.

```agda
postulate
  id⇒ :
    {Γ : Ctx} {D E : DTy Γ} →
    (φ : D ⇝ E) → φ ⇒ φ

  _∘⇒_ :
    {Γ : Ctx} {D E : DTy Γ} {φ ψ χ : D ⇝ E} →
    ψ ⇒ χ → φ ⇒ ψ → φ ⇒ χ

  lax-inv :
    {Γ : Ctx} {D E : DTy Γ} {φ ψ : D ⇝ E} →
    φ ⇒ ψ → ψ ⇒ φ

  lax-lwhisk :
    {Γ : Ctx} {D E F : DTy Γ} →
    (φ : D ⇝ E) {ψ χ : E ⇝ F} →
    ψ ⇒ χ → (ψ ∘⇝ φ) ⇒ (χ ∘⇝ φ)

  lax-rwhisk :
    {Γ : Ctx} {D E F : DTy Γ} {φ ψ : D ⇝ E} →
    φ ⇒ ψ → (χ : E ⇝ F) → (χ ∘⇝ φ) ⇒ (χ ∘⇝ ψ)
```

## Evaluation at points of the source diagram

A morphism `φ : D ⇝ E` evaluates a point `d : DTm D` of the source diagram to a point of
the target, `apply-diag-mor φ d : DTm E` — the composite of the relative section `map φ`
with `d`. The hom/lax helpers transport ordinary diagram-hom terms (`dhom` from
`4b-DiagramHoms-Comp`) along this evaluation: a morphism acts functorially on homs, the
identity morphism comes with a comparison cell, composition is compatible with
evaluation, and a lax transformation yields a comparison hom between the two evaluations.
These are exposed as chosen operations; their semantics are evaluation of relative
sections and relative homs (replacing the old `dty-proj` / shape-equality machinery).

```agda
postulate
  apply-diag-mor :
    {Γ : Ctx} {D E : DTy Γ} →
    D ⇝ E → DTm D → DTm E

  apply-diag-mor-hom :
    {Γ : Ctx} {D E : DTy Γ} →
    (φ : D ⇝ E) →
    {d e : DTm D} →
    DTm (dhom d e) →
    DTm (dhom (apply-diag-mor φ d) (apply-diag-mor φ e))

  apply-id-diag-mor-hom :
    {Γ : Ctx} {D : DTy Γ} →
    (d : DTm D) →
    DTm (dhom d (apply-diag-mor (id⇝ D) d))

  apply-diag-mor-comp-hom :
    {Γ : Ctx} {D E F : DTy Γ} →
    (φ : D ⇝ E) →
    (ψ : E ⇝ F) →
    (d : DTm D) →
    DTm
      (dhom
        (apply-diag-mor (ψ ∘⇝ φ) d)
        (apply-diag-mor ψ (apply-diag-mor φ d)))

  apply-lax-transformation :
    {Γ : Ctx} {D E : DTy Γ} →
    {φ ψ : D ⇝ E} →
    φ ⇒ ψ →
    (d : DTm D) →
    DTm (dhom (apply-diag-mor φ d) (apply-diag-mor ψ d))
```

