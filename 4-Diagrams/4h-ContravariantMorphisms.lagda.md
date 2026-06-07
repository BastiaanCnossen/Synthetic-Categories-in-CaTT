# 4h-ContravariantMorphisms: morphisms of contravariant families

This module is the production-facing compatibility layer between
`4f-Contravariance` and the current diagram-morphism/equivalence files.

The point is deliberately modest: a morphism of contravariant families is just a
diagram morphism between the underlying telescopes over `Γ ▸ ⋆`, and an
equivalence is just the corresponding diagram equivalence. What is not yet
available in the active `4a`/`4d` setup is the full reindexing operation for
relative sections `DTmOverDTy` along arbitrary base substitutions. Consequently,
the pointwise restriction of family morphisms and the functoriality of pointwise
equivalences are recorded as explicit bridges here.

```agda
module 4h-ContravariantMorphisms where

open import 2a-CaTT-Comp
open import 4a-Diagrams-Comp
open import 4f-Contravariance-Comp public
open import 2c-BasicCoherences-Comp
  using (Obj; Mor; id; _•₁_; _[_]obj)

import 4d-DiagramMorphisms as DM
import 4e-DiagramEquivalences as DE

open DM public using
  ( _⇝_; DTm; dhom
  ; apply-diag-mor; apply-diag-mor-hom
  )

open import 4g-ArrowDiagrams public
  using (arrow-conv-DTy; get-arrow)
```

## Family Morphisms And Equivalences

These are only aliases over the active diagram-morphism layer. A contravariant
family `D : conv-DTy Γ` is a diagram type over the apex context `Γ ▸ ⋆`, so its
family morphisms and equivalences are the ordinary ones between those underlying
diagram types.

```agda
conv-DTy-morph :
  {Γ : Ctx} →
  conv-DTy Γ →
  conv-DTy Γ →
  Set₁
conv-DTy-morph D E = conv-DTy.dty D ⇝ conv-DTy.dty E

conv-DEquiv :
  {Γ : Ctx} →
  conv-DTy Γ →
  conv-DTy Γ →
  Set₁
conv-DEquiv D E = DE.DEquiv (conv-DTy.dty D) (conv-DTy.dty E)
```

## Pointwise Restriction

`Fiber-morphism φ a` is the restriction of a morphism of contravariant families
to the fiber at `a`. Semantically this is reindexing the relative section
underlying `φ` along `inst-obj a`. This is now a **definition**: the fiber
telescopes `Fiber D a` / `Fiber E a` are the diagram substitutions of the family
telescopes along `inst-obj a` (recognised by `substDTy-rel`), and base-change of the
underlying relative section is `substDTmOverDTy-fun` from `4a-Diagrams-Comp`. (The
base-change/action commutation lemma needed to *prove* `substDTmOverDTy-fun` correct
is still postulated there; here we only consume its computed output.)

```agda
Fiber-morphism :
  {Γ : Ctx} →
  {D E : conv-DTy Γ} →
  conv-DTy-morph D E →
  (a : Obj Γ) →
  Fiber D a ⇝ Fiber E a
Fiber-morphism {Γ} {D = D} {E = E} φ a =
  record
    { map =
        substDTmOverDTy-fun
          (substDTy-rel (inst-obj a) (conv-DTy.dty D))
          (substDTy-rel (inst-obj a) (conv-DTy.dty E))
          (DM.map φ) }
```

The same missing pointwise functoriality is needed to derive equivalences on
fibers from equivalences of family telescopes. We keep the intended pointwise
equivalence as an explicit bridge.

```agda
postulate
  Fiber-DEquiv :
    {Γ : Ctx} →
    {D E : conv-DTy Γ} →
    (φ : conv-DEquiv D E) →
    (a : Obj Γ) →
    DE.DiagramEquiv
      (Fiber-morphism {D = D} {E = E} (DE.DEquiv.map φ) a)
```

The unit and counit helpers are definable once the pointwise equivalence bridge is
chosen. Their types are phrased using the active `DM.dhom`,
`DM.apply-diag-mor`, and `DE.from` fields.

```agda
Fiber-DEquiv-unit-hom-type :
  {Γ : Ctx} →
  {D E : conv-DTy Γ} →
  (φ : conv-DEquiv D E) →
  (a : Obj Γ) →
  DTm (Fiber D a) →
  Set₁
Fiber-DEquiv-unit-hom-type {D = D} {E = E} φ a d =
  DTm
    (DM.dhom
      d
      (DM.apply-diag-mor
        (DE.from (Fiber-DEquiv {D = D} {E = E} φ a))
        (DM.apply-diag-mor
          (Fiber-morphism {D = D} {E = E} (DE.DEquiv.map φ) a)
          d)))

Fiber-DEquiv-counit-hom-type :
  {Γ : Ctx} →
  {D E : conv-DTy Γ} →
  (φ : conv-DEquiv D E) →
  (a : Obj Γ) →
  DTm (Fiber E a) →
  Set₁
Fiber-DEquiv-counit-hom-type {D = D} {E = E} φ a d =
  DTm
    (DM.dhom
      d
      (DM.apply-diag-mor
        (Fiber-morphism {D = D} {E = E} (DE.DEquiv.map φ) a)
        (DM.apply-diag-mor
          (DE.from (Fiber-DEquiv {D = D} {E = E} φ a))
          d)))

Fiber-DEquiv-unit-hom :
  {Γ : Ctx} →
  {D E : conv-DTy Γ} →
  (φ : conv-DEquiv D E) →
  (a : Obj Γ) →
  (d : DTm (Fiber D a)) →
  Fiber-DEquiv-unit-hom-type {D = D} {E = E} φ a d
Fiber-DEquiv-unit-hom {D = D} {E = E} φ a d =
  DE.diagram-equiv-unit-hom
    (Fiber-DEquiv {D = D} {E = E} φ a)
    d

Fiber-DEquiv-counit-hom :
  {Γ : Ctx} →
  {D E : conv-DTy Γ} →
  (φ : conv-DEquiv D E) →
  (a : Obj Γ) →
  (d : DTm (Fiber E a)) →
  Fiber-DEquiv-counit-hom-type {D = D} {E = E} φ a d
Fiber-DEquiv-counit-hom {D = D} {E = E} φ a d =
  DE.diagram-equiv-counit-hom
    (Fiber-DEquiv {D = D} {E = E} φ a)
    d
```

## Chosen Contravariant Action

The `conv-DTy` record now carries its contravariant action as the `action` field, so
the chosen action is simply `conv-DTy.action D`; there is no longer a global
postulate that every family has one. The term-level pullback wrappers are just
projections from that field.

```agda
conv-pullback :
  {Γ : Ctx} {s t : Obj Γ} →
  (D : conv-DTy Γ) →
  Mor s t →
  DTm (Fiber D t) →
  DTm (Fiber D s)
conv-pullback {Γ = Γ} {s = s} {t = t} D h d =
  ContravariantAction.pullback (conv-DTy.action D) (idS Γ) s t
    (Fiber-is-fiber {D = D} {σ = idS Γ} {a = s})
    (Fiber-is-fiber {D = D} {σ = idS Γ} {a = t}) h d

conv-pullback-hom :
  {Γ : Ctx} {s t : Obj Γ} →
  (D : conv-DTy Γ) →
  (h : Mor s t) →
  {d d′ : DTm (Fiber D t)} →
  DTm (DM.dhom d d′) →
  DTm
    (DM.dhom
      (conv-pullback D h d)
      (conv-pullback D h d′))
conv-pullback-hom {Γ = Γ} {s = s} {t = t} D h {d} {d′} p =
  ContravariantAction.pullback-hom (conv-DTy.action D) (idS Γ)
    (Fiber-is-fiber {D = D} {σ = idS Γ} {a = s})
    (Fiber-is-fiber {D = D} {σ = idS Γ} {a = t}) h
    (DM.dhom-is-DHom d d′) p
    (DM.dhom-is-DHom (conv-pullback D h d) (conv-pullback D h d′))

conv-pullback-id :
  {Γ : Ctx} {x : Obj Γ} →
  (D : conv-DTy Γ) →
  (d : DTm (Fiber D x)) →
  DTm
    (DM.dhom
      d
      (conv-pullback D (id x) d))
conv-pullback-id {Γ = Γ} {x = x} D d =
  ContravariantAction.pullback-id (conv-DTy.action D) (idS Γ) x
    (Fiber-is-fiber {D = D} {σ = idS Γ} {a = x}) d
    (DM.dhom-is-DHom d (conv-pullback D (id x) d))

conv-pullback-comp :
  {Γ : Ctx} {x y z : Obj Γ} →
  (D : conv-DTy Γ) →
  (f : Mor x y) →
  (g : Mor y z) →
  (d : DTm (Fiber D z)) →
  DTm
    (DM.dhom
      (conv-pullback D f (conv-pullback D g d))
      (conv-pullback D (g •₁ f) d))
conv-pullback-comp {Γ = Γ} {x = x} {y = y} {z = z} D f g d =
  ContravariantAction.pullback-assoc
    (conv-DTy.action D)
    (idS Γ)
    x y z
    (Fiber-is-fiber {D = D} {σ = idS Γ} {a = x})
    (Fiber-is-fiber {D = D} {σ = idS Γ} {a = y})
    (Fiber-is-fiber {D = D} {σ = idS Γ} {a = z})
    g
    f
    d
    (DM.dhom-is-DHom
      (conv-pullback D f (conv-pullback D g d))
      (conv-pullback D (g •₁ f) d))
```

`conv-action D h` is the diagram-morphism (internal) form of the contravariant
action: the termwise pullback packaged as a relative section `Fiber D t ⇝ Fiber D s`.
Packaging the termwise pullback as an internal morphism is not yet carried out, so
`conv-action` is postulated, together with its identity and composition coherences
(the comparison cells against the identity / composite morphisms, stated at the level
of `apply-diag-mor`, which lives in `4d`).

```agda
postulate
  conv-action :
    {Γ : Ctx} {s t : Obj Γ} →
    (D : conv-DTy Γ) →
    Mor s t →
    Fiber D t ⇝ Fiber D s

  conv-action-id :
    {Γ : Ctx} {x : Obj Γ} →
    (D : conv-DTy Γ) →
    (d : DTm (Fiber D x)) →
    DTm
      (DM.dhom
        d
        (DM.apply-diag-mor (conv-action D (id x)) d))

  conv-action-comp :
    {Γ : Ctx} {x y z : Obj Γ} →
    (D : conv-DTy Γ) →
    (f : Mor x y) →
    (g : Mor y z) →
    (d : DTm (Fiber D z)) →
    DTm
      (DM.dhom
        (DM.apply-diag-mor (conv-action D f)
          (DM.apply-diag-mor (conv-action D g) d))
        (DM.apply-diag-mor (conv-action D (g •₁ f)) d))
```

The action on diagram hom terms is already part of the active morphism evaluation
API.

```agda
conv-action-hom :
  {Γ : Ctx} {s t : Obj Γ} →
  (D : conv-DTy Γ) →
  (h : Mor s t) →
  {d d′ : DTm (Fiber D t)} →
  DTm (DM.dhom d d′) →
  DTm
    (DM.dhom
      (DM.apply-diag-mor (conv-action D h) d)
      (DM.apply-diag-mor (conv-action D h) d′))
conv-action-hom D h =
  DM.apply-diag-mor-hom (conv-action D h)
```

Naturality of the contravariant action in the family morphism is another pointwise
functoriality bridge. Its intended semantics are that pulling back after applying a
family morphism agrees, up to diagram-morphism isomorphism, with applying the family
morphism after pulling back.

```agda
postulate
  conv-action-nat :
    {Γ : Ctx} {D E : conv-DTy Γ} →
    (φ : conv-DTy-morph D E) →
    {s t : Obj Γ} →
    (h : Mor s t) →
    DE.Properties.DiagramMorIso
      (conv-action E h DM.∘⇝
        Fiber-morphism {D = D} {E = E} φ t)
      (Fiber-morphism {D = D} {E = E} φ s DM.∘⇝
        conv-action D h)
```

## The Yoneda action bridge

The Yoneda map is the **generic internalization of contravariant pullback along the
generic arrow**. A chosen element `τ : DTm (Fiber D x)` induces a morphism of
families `arrow-conv-DTy x ⇝ D` that, fibrewise at `a`, sends an arrow `h : a → x`
(a fiber term of the arrow family) to the pullback `h*(τ) : D(a)`. This is exactly
the data the Yoneda file `5a` used to postulate directly; it conceptually belongs
here, next to the contravariant action it internalizes.

It is still **postulated**. It would be built from the internal action `conv-action`
(itself postulated above) by *evaluation along the generic arrow* of
`arrow-conv-DTy x`, together with the arrow family's representability (`get-arrow`),
and that construction is not yet carried out. Moving the bridge here places the axiom
beside the action infrastructure it depends on, so that `5a` can become a thin
re-export.

```agda
postulate
  conv-action-yoneda :
    {Γ : Ctx} {D : conv-DTy Γ} →
    (x : Obj Γ) →
    DTm (Fiber D x) →
    conv-DTy-morph (arrow-conv-DTy x) D

  conv-action-yoneda-β :
    {Γ : Ctx} {D : conv-DTy Γ} {x : Obj Γ} →
    (τ : DTm (Fiber D x)) →
    (a : Obj Γ) →
    (hS : DTm (Fiber (arrow-conv-DTy x) a)) →
    DTm
      (DM.dhom
        (DM.apply-diag-mor
          (Fiber-morphism
            {D = arrow-conv-DTy x}
            {E = D}
            (conv-action-yoneda {Γ = Γ} {D = D} x τ)
            a)
          hS)
        (DM.apply-diag-mor
          (conv-action D (get-arrow hS))
          τ))

  conv-action-yoneda-nat :
    {Γ : Ctx} {D E : conv-DTy Γ} →
    (φ : conv-DTy-morph D E) →
    (x : Obj Γ) →
    (τ : DTm (Fiber D x)) →
    DE.Properties.DiagramMorIso
      (conv-action-yoneda {Γ = Γ} {D = E} x
        (DM.apply-diag-mor
          (Fiber-morphism {D = D} {E = E} φ x)
          τ))
      (φ DM.∘⇝ conv-action-yoneda {Γ = Γ} {D = D} x τ)
```

### Audit: how `conv-action-yoneda` should eventually be derived

The right first-principles route is option (1)→(2) below, not a transport rebuild:

1. **Package the termwise pullback as the internal action `conv-action`** — turn the
   termwise `pullback` (on closed points) into a relative section
   `Fiber D t ⇝ Fiber D s`. This is the relative-section form the rest of the
   construction builds on; it is currently postulated.
2. **Obtain `conv-action-yoneda` as evaluation along the generic arrow.** The Yoneda
   morphism should be `conv-action` of the generic arrow of `arrow-conv-DTy x` applied
   to `τ` — i.e. the family-level version of `conv-action-eval` — packaged as a
   relative section over the apex context. The β-law is then the arrow family's
   precomposition β-law (`arrow-pullback-β` in `4h`) transported along this
   construction. This step is what remains postulated.
3. A purely **structural** construction directly from `is-contravar-DTy` (building
   the section by recursion on the contravariance witness) is the deepest version,
   but it presupposes the naturality-of-diagram-types machinery that would also
   *produce* the `action` field of `conv-DTy` in the first place. That derivation is
   deliberately out of scope: the action is intentionally assumed as part of the
   `conv-DTy` data for now.
