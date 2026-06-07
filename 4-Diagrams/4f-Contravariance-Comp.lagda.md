# 4f-Contravariance-Comp: computed representatives for contravariant families

This is the **computational companion** to the relation-first `4f-Contravariance`.
It re-exports the core and adds the *computed* representatives that the relational
core deliberately avoids:

- the instantiation substitution `inst-obj` and the base-change lift
  `apex-lift-sub` (the apex substitution `apex-sub` itself is in the core);
- the computed fibers `Fiber` and the computed base-change of a
  family `conv-DTy-sub`;
- the **satisfaction witness** `Fiber-is-fiber`, tying the computed `Fiber`
  to the core recognizer `IsFiber`.

Importing the computational modules is allowed here. Downstream files that need
concrete `Fiber` diagram types (currently `4g`, `4h`, `5a`) import
this companion rather than the core.

A few witnesses are postulated where proving them would require large raw
substitution plumbing or the (still missing) preservation of contravariance under
substitution. These postulates live here, never in the core.

```agda
module 4f-Contravariance-Comp where

import 1a-RawSyntax-Comp as Raw
open import 2a-CaTT-Comp
open import 4a-Diagrams-Comp
open import 4b-DiagramHoms-Comp
open import 2c-BasicCoherences-Comp using (Obj)

open import 4f-Contravariance public
```

## Apex substitutions

`apex-sub` is now defined in the core (with a canonical well-formedness witness), so
here we only add the special cases. `inst-obj` is `apex-sub` at the computed identity
`idS Γ`.

```agda
inst-obj : {Γ : Ctx} → Obj Γ → Sub Γ (Γ ▸ ⋆)
inst-obj {Γ} t = apex-sub (idS Γ) t
```

The base-change lift `apex-lift-sub σ : Sub (Δ ▸ ⋆) (Γ ▸ ⋆)` lifts `σ` across the
apex object. It is simply `apex-sub` over the weakened base `σ ∘ wk`, applied to the
apex object `apex-Obj`.

```agda
apex-lift-sub : {Γ Δ : Ctx} → Sub Δ Γ → Sub (Δ ▸ ⋆) (Γ ▸ ⋆)
apex-lift-sub {Δ = Δ} σ = apex-sub (σ ∘ wk {A = ⋆ {Γ = Δ}}) (apex-Obj {Γ = Δ})
```

## Computed fibers

The **fiber** of a contravariant family `D` at an object `t : Obj Δ`, taken after a
parameter substitution `σ : Sub Δ Γ`, instantiates the apex at `t` and substitutes
the telescope to `Δ`.

```agda
Fiber :
  {Γ Δ : Ctx} →
  conv-DTy Γ →
  Sub Δ Γ →
  Obj Δ →
  DTy Δ
Fiber D σ t =
  conv-DTy.dty D [ apex-sub σ t ]dT
```

The satisfaction witnesses say the computed fibers are recognized by the core
relations. Both follow from `substDTy-rel`: the computed diagram substitution
`_[_]dT` is recognized by `SubstDTy`, carrying the lifted total substitution
`dty-liftS`.

```agda
Fiber-is-fiber :
  {Γ Δ : Ctx} → {D : conv-DTy Γ} → {σ : Sub Δ Γ} → {a : Obj Δ} →
  IsFiber (conv-DTy.dty D) σ a (Fiber D σ a)
    (dty-liftS (apex-sub σ a) (conv-DTy.dty D))
Fiber-is-fiber {D = D} {σ = σ} {a = a} =
  substDTy-rel (apex-sub σ a) (conv-DTy.dty D)
```

## Computed base-change of a family

`conv-DTy-sub D σ` reindexes a contravariant family along `σ`. Its telescope is the
diagram substitution of the telescope of `D` along `apex-lift-sub σ`. Two pieces are
postulated here: that the result is again contravariant in the apex (preservation of
contravariance under substitution), and the **reindexed action**
`conv-DTy-sub-action`. Since the contravariant action is assumed structure (it is not
derived), transporting a chosen action along a base substitution is likewise deferred:
we simply postulate that the reindexed family carries one.

```agda
postulate
  conv-DTy-sub-is-contravar :
    {Γ Δ : Ctx} → (D : conv-DTy Γ) → (σ : Sub Δ Γ) →
    is-contravar-DTy (apex-objVar {Δ})
      (conv-DTy.dty D [ apex-lift-sub σ ]dT)

  conv-DTy-sub-action :
    {Γ Δ : Ctx} → (D : conv-DTy Γ) → (σ : Sub Δ Γ) →
    ContravariantAction
      (conv-DTy.dty D [ apex-lift-sub σ ]dT)
      (conv-DTy-sub-is-contravar D σ)

conv-DTy-sub :
  {Γ Δ : Ctx} →
  conv-DTy Γ →
  Sub Δ Γ →
  conv-DTy Δ
conv-DTy-sub D σ =
  mkConvDTy
    (conv-DTy.dty D [ apex-lift-sub σ ]dT)
    (conv-DTy-sub-is-contravar D σ)
    (conv-DTy-sub-action D σ)
```
