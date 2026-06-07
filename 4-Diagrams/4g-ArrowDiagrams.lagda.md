# 4g-ArrowDiagrams: the arrow diagram family

Fix an object `x : Obj Γ`. The **arrow diagram** at `x` is the contravariant
family whose fiber at an object `a` is the diagram of arrows `a → x`. In other
words it represents the functor

```text
a  ↦  Hom(a , x).
```

Concretely it is a single-component telescope over the apex context `Γ ▸ ⋆`: the one
component is the hom-type from the apex variable to (the weakening of) `x`.
Instantiating the apex at an object `a` makes the component `a → x`, so a diagram
term of the fiber is exactly an arrow `a → x`.

Its contravariant action is **precomposition**: pulling an arrow `t → x` back along
`h : s → t` yields the composite `s → x`. We package this fact, together with the
extraction/injection between fiber terms and morphisms, as a precise interface. The
representability computation principles — the round-trip laws and the
precomposition β-law — are recorded as postulates here; deriving them belongs to a
later pass and would otherwise require transporting along the computed substitution
that defines the fiber.

```agda
module 4g-ArrowDiagrams where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import 2a-CaTT-Comp
import 3a-UpClosed-Comp as Sel
open import 4a-Diagrams-Comp
open import 4b-DiagramHoms-Comp
open import 4f-Contravariance-Comp
open import 2c-BasicCoherences-Comp
  using ( Obj; Mor; Mor₂; _[_]obj; [⋆]_⇒_; _•₁_ )
```

## The arrow telescope

The single component is the arrow from the apex variable to `x` (weakened into the
apex context).

```agda
arrow-ty : {Γ : Ctx} → Obj Γ → Ty (Γ ▸ ⋆)
arrow-ty {Γ} x =
  [⋆] var-obj (apex-objVar {Γ}) ⇒ (x [ wk {Γ = Γ} {A = ⋆} ]obj)

arrow-DTy : {Γ : Ctx} → Obj Γ → DTy (Γ ▸ ⋆)
arrow-DTy x = ◆ᵈ ▸ᵈ arrow-ty x
```

The telescope is contravariant in the apex: its one component is an iterated hom
(here a single hom) whose source is the apex variable and whose target `x [ wk ]`
does not mention the apex.

```agda
arrow-DTy-is-conv :
  {Γ : Ctx} →
  (x : Obj Γ) →
  is-contravar-DTy apex-objVar (arrow-DTy x)
arrow-DTy-is-conv {Γ} x =
  ext (apex-objVar {Γ}) ◆ᵈ (base (apex-objVar {Γ})) (arrow-ty x)
    (record
      { tgt-obj = x [ wk {Γ = Γ} {A = ⋆} ]obj
      ; bdry    = bdry-base
      ; tgt     = Sel.var-upclose-zero-wk-no-dep {Γ = Γ} {A = ⋆} (Obj.tm x)
      })
```

The contravariant action of the arrow family is **precomposition**. As with every
`conv-DTy`, the action is part of the data; we postulate it here (over the telescope
and its contravariance witness, so that it can be supplied as the `action` field of
`arrow-conv-DTy`). Its computation rules appear further below.

```agda
postulate
  arrow-action :
    {Γ : Ctx} →
    (x : Obj Γ) →
    ContravariantAction (arrow-DTy x) (arrow-DTy-is-conv x)

arrow-conv-DTy : {Γ : Ctx} → Obj Γ → conv-DTy Γ
arrow-conv-DTy x =
  mkConvDTy
    (arrow-DTy x)
    (arrow-DTy-is-conv x)
    (arrow-action x)
```

## Fiber terms versus arrows

The fiber of the arrow family at `a` is the diagram type of arrows `a → x`, so its
diagram terms are in bijection with morphisms `a → x`. We expose both directions of
that bijection. Their definitions transport across the computed substitution that
defines `Fiber`, which we elide here; they are recorded as the
representability interface of the arrow family.

```agda
postulate
  get-arrow :
    {Γ : Ctx} {a x : Obj Γ} →
    DTm (Fiber (arrow-conv-DTy x) a) →
    Mor a x

  arrow-dtm :
    {Γ : Ctx} {a x : Obj Γ} →
    Mor a x →
    DTm (Fiber (arrow-conv-DTy x) a)
```

The round-trip laws state that the bijection is genuine. The first is a strict
equality; the second is phrased as a hom term, the direction that type-checks
naturally for diagram terms.

```agda
postulate
  get-arrow-arrow-dtm :
    {Γ : Ctx} {a x : Obj Γ} →
    (h : Mor a x) →
    get-arrow (arrow-dtm h) ≡ h

  arrow-dtm-get-arrow :
    {Γ : Ctx} {a x : Obj Γ} →
    (d : DTm (Fiber (arrow-conv-DTy x) a)) →
    DTm (dhom d (arrow-dtm (get-arrow d)))
```

The arrow fiber is a diagram presentation of the hom type `a → x`, so homs in the
fiber reflect to 2-cells between the extracted arrows. These witnesses are the
hom-level part of the representability interface; deriving them requires
transporting the computed arrow-fiber hom telescope back to the ambient CaTT hom
type.

```agda
postulate
  get-arrow-hom :
    {Γ : Ctx} {a x : Obj Γ} →
    {h k : DTm (Fiber (arrow-conv-DTy x) a)} →
    DTm (dhom h k) →
    Mor₂ (get-arrow h) (get-arrow k)

  get-arrow-hom-arrow-dtm :
    {Γ : Ctx} {a x : Obj Γ} →
    {h : Mor a x} →
    {k : DTm (Fiber (arrow-conv-DTy x) a)} →
    DTm (dhom (arrow-dtm h) k) →
    Mor₂ h (get-arrow k)
```

## The contravariant action: precomposition

The action of the arrow family is precomposition; it was supplied as the `action`
field of `arrow-conv-DTy` above (the postulate `arrow-action`). Its β-law identifies
the underlying operation with composition.

The β-law: pulling back an arrow `d : t → x` along `h : s → t` is the composite
`(get-arrow d) ∘ h : s → x`.

```agda
postulate
  arrow-pullback-β :
    {Γ : Ctx} {x : Obj Γ} →
    {s t : Obj Γ} →
    (h : Mor s t) →
    (d : DTm (Fiber (arrow-conv-DTy x) t)) →
    get-arrow
      (pullback (arrow-action x) (idS Γ) s t
        (Fiber-is-fiber {D = arrow-conv-DTy x} {σ = idS Γ} {a = s})
        (Fiber-is-fiber {D = arrow-conv-DTy x} {σ = idS Γ} {a = t})
        h d)
      ≡
    (get-arrow d) •₁ h
```
