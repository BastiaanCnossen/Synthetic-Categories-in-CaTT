# 4f-Contravariance: contravariant diagram types (relational core)

A **contravariant diagram type** consists of:
- A digram type `D` over `Γ ▸ ⋆`, 
- A witness that it is contravariant: each entry has the apex variable as
      iterated source, while the target being different from the apex
- A chosen **chosen contravariant action**.

In principle, the contravariant action can be *constructed*. However, this
construction is intricate, and we will take it for granted in this file.

By instantiating the apex by some object `a : Obj Γ`, we obtain the *fiber* 
`D(a)` of `D` at `a`. 

This file is the **relation-first core**. It carries no `*-Comp` imports and
introduces no computed substitutions or computed fibers. 

The computed representatives live in the companion `4f-Contravariance-Comp`.

```agda
module 4f-Contravariance where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

import 1a-RawSyntax as Raw
open import 2a-CaTT
import 3a-UpClosed as Sel
open import 4a-Diagrams
open import 4b-DiagramHoms using (DHom)
open import 2c-BasicCoherences
  using ( Obj; mkObj; Mor; id; _•₁_; [⋆]_⇒_ )
```

## Object-variables and the apex

An *object-variable* `x : ObjVar Γ` is a variable whose type is `⋆`. 
The *generic apex* `apex-objVar` is the last variable of the context `Γ ▸ ⋆`.

```agda
record ObjVar (Γ : Ctx) : Set₁ where
  constructor mkObjVar
  field
    obj-var       : Var Γ
    obj-var-hasTy : HasTyVar obj-var (⋆ {Γ = Γ})

open ObjVar public

var-obj : {Γ : Ctx} → ObjVar Γ → Obj Γ
var-obj x = mkObj (var (obj-var x)) (Raw.varTy (obj-var-hasTy x))

apex-objVar : {Γ : Ctx} → ObjVar (Γ ▸ ⋆)
apex-objVar {Γ} = mkObjVar (zero {Γ = Γ} {A = ⋆}) (Raw.zeroTy Raw.wk-⋆)

apex-Obj : {Γ : Ctx} → Obj (Γ ▸ ⋆)
apex-Obj {Γ} = var-obj (apex-objVar {Γ})
```

Given a substitution `σ : Sub Δ Γ` and an object `a : Obj Δ`, the associated 
*apex substitution* extends `σ` by `a`.

```agda
apex-sub : {Γ Δ : Ctx} → (σ : Sub Δ Γ) → Obj Δ → Sub Δ (Γ ▸ ⋆)
apex-sub σ a = ⟨ σ , Obj.tm a ⟩:[ Raw.typed-sub Raw.sub-⋆ (Obj.hasTy a) ]
```

## Lifting variables through a diagram type

Any variable in `Γ` lifts to one in `Γ ▸▸ D`. This preserves object-variables.

```agda
dty-var : {Γ : Ctx} → (D : DTy Γ) → Var Γ → Var (Γ ▸▸ D)
dty-var ◆ᵈ x = x
dty-var {Γ} (D ▸ᵈ A) x = succ {Γ = Γ ▸▸ D} {A = A} (dty-var D x)

dty-var-⋆-hasTyVar : {Γ : Ctx} → (D : DTy Γ) → (x : Var Γ) →
  HasTyVar x (⋆ {Γ = Γ}) → HasTyVar (dty-var D x) (⋆ {Γ = Γ ▸▸ D})
dty-var-⋆-hasTyVar ◆ᵈ x p = p
dty-var-⋆-hasTyVar (D ▸ᵈ A) x p =
  Raw.succTy {B = Raw-Ty A} (dty-var-⋆-hasTyVar D x p) Raw.wk-⋆

dty-objVar : {Γ : Ctx} → (D : DTy Γ) → ObjVar Γ → ObjVar (Γ ▸▸ D)
dty-objVar D x =
  mkObjVar
    (dty-var D (obj-var x))
    (dty-var-⋆-hasTyVar D (obj-var x) (obj-var-hasTy x))
```

## Contravariant diagram types

For defining contravariant types, we first recognize the 0-dimensional source
and target of a type.

```agda
data ObjBdry {Γ : Ctx} : Ty Γ → Obj Γ → Obj Γ → Set₁ where
  bdry-base :
    {s t : Obj Γ} →
    ObjBdry ([⋆] s ⇒ t) s t

  bdry-step :
    {A : Ty Γ} {u v : Tm Γ}
    {pu : HasTy u A} {pv : HasTy v A}
    {s t : Obj Γ} →
    ObjBdry A s t →
    ObjBdry (homTy A u v pu pv) s t
```

Consider a context `Γ`, and let `x` by an object-variable. A type `A` is 
*contravariant in `x`* when it is an iterated hom whose source is `x` and 
whose target `tgt-obj` does **not** depend on `x`.

```agda
record is-contravar-Ty {Γ : Ctx} (A : Ty Γ) (x : ObjVar Γ) : Set₁ where
  field
    tgt-obj : Obj Γ
    bdry    : ObjBdry A (var-obj x) tgt-obj
    tgt     : Sel.tm-dep (Sel.var-upclose (obj-var x)) (Obj.tm tgt-obj) → ⊥
```

A diagram telescope is contravariant when each of its components is.

```agda
data is-contravar-DTy {Γ : Ctx} : ObjVar Γ → DTy Γ → Set₁ where
  base : (x : ObjVar Γ)
    → is-contravar-DTy x ◆ᵈ
  ext : (x : ObjVar Γ)
    → (D : DTy Γ) → is-contravar-DTy x D
    → (B : Ty (Γ ▸▸ D)) → is-contravar-Ty {Γ ▸▸ D} B (dty-objVar D x)
    → is-contravar-DTy x (D ▸ᵈ B)

open is-contravar-DTy public
```

## Fibers

Let `D : DTy (Γ ▸ ⋆)` by a diagram type. For every substitution `σ : Sub Δ Γ` and
every object `a : Obj Δ`, we obtain a new diagram type `D(a) : DTy Δ` by substituting
`D` along `apex-sub σ a : Sub Δ (Γ ▸ ⋆)`.

The relation `IsFiber D σ a F ρ` says that `F : DTy Δ` is the fiber `D(a)`: it
is the diagram substitution of `D` along `apex-sub σ a`, with lifted total
substitution `ρ`. We expose `ρ` as an explicit argument (it is just the `SubstDTy`
relation at `apex-sub σ a`) rather than hiding it in an existential.

```agda
IsFiber :
  {Γ Δ : Ctx} →
  (D : DTy (Γ ▸ ⋆)) →
  (σ : Sub Δ Γ) →
  (a : Obj Δ) →
  (F : DTy Δ) →
  Sub (Δ ▸▸ F) ((Γ ▸ ⋆) ▸▸ D) →
  Set₁
IsFiber D σ a F ρ = SubstDTy (apex-sub σ a) D F ρ
```

## The contravariant action

We now record the precise shape the contravariant action of a contravariant diagram
type should take. 

Because fibers are no longer computed diagram types, every operation consumes the
fiber diagram types **explicitly**, together with `IsFiber` witnesses that they
are the relevant fibers. The functoriality and coherence laws are stated
relationally as well: rather than referring to a computed `dhom`, they produce a
diagram term of an *arbitrary* hom carrier `H` recognized by `DHom`.

```agda
record ContravariantAction {Γ : Ctx}
  (D : DTy (Γ ▸ ⋆))
  (isD : is-contravar-DTy (apex-objVar {Γ = Γ}) D) : Set₁ where
  field
    pullback :
      {Δ : Ctx} →
      (σ : Sub Δ Γ) →
      (s t : Obj Δ) →
      {Fs Ft : DTy Δ} →
      {ρs : Sub (Δ ▸▸ Fs) ((Γ ▸ ⋆) ▸▸ D)} →
      {ρt : Sub (Δ ▸▸ Ft) ((Γ ▸ ⋆) ▸▸ D)} →
      IsFiber D σ s Fs ρs →
      IsFiber D σ t Ft ρt →
      Mor s t →
      DTm Ft →
      DTm Fs

    pullback-hom :
      {Δ : Ctx} →
      (σ : Sub Δ Γ) →
      {s t : Obj Δ} →
      {Fs Ft : DTy Δ} →
      {ρs : Sub (Δ ▸▸ Fs) ((Γ ▸ ⋆) ▸▸ D)} →
      {ρt : Sub (Δ ▸▸ Ft) ((Γ ▸ ⋆) ▸▸ D)} →
      (fs : IsFiber D σ s Fs ρs) →
      (ft : IsFiber D σ t Ft ρt) →
      (h : Mor s t) →
      {d d′ : DTm Ft} →
      {Hd : DTy Δ} → DHom d d′ Hd → DTm Hd →
      {Hp : DTy Δ} →
      DHom (pullback σ s t fs ft h d) (pullback σ s t fs ft h d′) Hp →
      DTm Hp

    pullback-id :
      {Δ : Ctx} →
      (σ : Sub Δ Γ) →
      (s : Obj Δ) →
      {Fs : DTy Δ} →
      {ρs : Sub (Δ ▸▸ Fs) ((Γ ▸ ⋆) ▸▸ D)} →
      (fs : IsFiber D σ s Fs ρs) →
      (d : DTm Fs) →
      {H : DTy Δ} →
      DHom d (pullback σ s s fs fs (id s) d) H →
      DTm H

    pullback-assoc :
      {Δ : Ctx} →
      (σ : Sub Δ Γ) →
      (r s t : Obj Δ) →
      {Fr Fs Ft : DTy Δ} →
      {ρr : Sub (Δ ▸▸ Fr) ((Γ ▸ ⋆) ▸▸ D)} →
      {ρs : Sub (Δ ▸▸ Fs) ((Γ ▸ ⋆) ▸▸ D)} →
      {ρt : Sub (Δ ▸▸ Ft) ((Γ ▸ ⋆) ▸▸ D)} →
      (fr : IsFiber D σ r Fr ρr) →
      (fs : IsFiber D σ s Fs ρs) →
      (ft : IsFiber D σ t Ft ρt) →
      (h : Mor s t) →
      (k : Mor r s) →
      (d : DTm Ft) →
      {H : DTy Δ} →
      DHom
        (pullback σ r s fr fs k (pullback σ s t fs ft h d))
        (pullback σ r t fr ft (h •₁ k) d)
        H →
      DTm H

open ContravariantAction public
```

## Contravariant diagram types

We define a **contravariant diagram type** `conv-DTy Γ` by bundling three things:
- A digram type over `Γ ▸ ⋆`, 
- A witness that it is contravariant
- A chosen **chosen contravariant action**.

```agda
record conv-DTy (Γ : Ctx) : Set₁ where
  constructor mkConvDTy
  field
    dty          : DTy (Γ ▸ ⋆)
    is-contravar : is-contravar-DTy (apex-objVar {Γ = Γ}) dty
    action       : ContravariantAction dty is-contravar

open conv-DTy public
```
