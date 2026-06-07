# 2a-CaTT: Intrinsic CaTT over Raw Syntax

This module gives the intrinsic CaTT syntax built directly over the
raw syntax. We define the well-formedness of types and substitutions using the 
inductive raw typing relation `Raw.HasTy`.

This file is the **relational core**. It imports only the relational `1-preCaTT`
modules and holds the proposition-facing material: the inductive well-formedness
relations, the proof-carrying records, the public context layer, the
relation-native constructors, and the typed wrappers for the relational 
pasting/dimension API. 

Everything that needs a *computed* raw operation (`wkTy`, `_[_]T`, `_∘_`, `idS`, 
`lookup`, `var-to-type`, `tyOf`, the computed equational theory, and the `tyOf` ↔ 
`HasTy` bridges) lives in the companion module `2a-CaTT-Comp`.

The file has two layers:

1. An inner raw-indexed implementation layer works over raw contexts
   of type `RawCtx`. There we define `Ctx-iswf`, `Ty-iswf`, `Tm-iswf`, and
   `Sub-iswf`, and build the proof-carrying records.
2. The outer part packages a raw context with a well-formedness proof as the
   public `Ctx`, and reindexes `Ty`, `Tm`, `Sub` over that packaged context.

Later parts of the file establish basic results and user interface.

```agda
module 2a-CaTT where

import 1a-RawSyntax as Raw
import 1c-Pasting as Ps
import 1d-Fullness as Full

open import Data.Nat using (ℕ; suc; _⊔_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂; subst)

module P = Ps
module F = Full

open Raw using (RawCtx; RawTy; RawTm; RawSub; RawVar)
open F public using (Full)
```

## Inner Raw-Indexed Layer

The inner layer is indexed over raw contexts. It defines:
- The four well-formedness predicates (`Ctx-iswf`, `Ty-iswf`, `Tm-iswf`, `Sub-iswf`)
- The records `TyR`, `TmR`, `SubR` which bundle a raw term with its well-formedness proof

The outer layer below will re-index the inner layer over well-formed contexts; this
should be treated as the clean public API. To avoid clashes, the inner layer is named
with a trailing `R` (for "raw-indexed"). 

The structural operations on these records (`_[_]TR`, `_[_]tR`, `_∘R_`, weakening, …) 
are computational and live in `2a-CaTT-Comp`.

```agda
mutual
  data Ctx-iswf : RawCtx → Set₁
  data Ty-iswf  : ∀ {Γ : RawCtx} → RawTy Γ → Set₁
  data Tm-iswf  : ∀ {Γ : RawCtx} → RawTm Γ → Set₁
  data Sub-iswf : ∀ {Γ Δ : RawCtx} → RawSub Γ Δ → Set₁

  record TyR (Γ : RawCtx) : Set₁ where
    pattern
    constructor mkTyR
    inductive
    field
      rawTyR  : RawTy Γ
      ty-iswf : Ty-iswf rawTyR

  record TmR (Γ : RawCtx) : Set₁ where
    pattern
    constructor mkTmR
    inductive
    field
      rawTmR  : RawTm Γ
      tm-iswf : Tm-iswf rawTmR

  record SubR (Γ Δ : RawCtx) : Set₁ where
    pattern
    constructor mkSubR
    inductive
    field
      rawSubR  : RawSub Γ Δ
      sub-iswf : Sub-iswf rawSubR

  Raw-TyR : ∀ {Γ : RawCtx} → TyR Γ → RawTy Γ
  Raw-TyR = TyR.rawTyR

  Raw-TmR : ∀ {Γ : RawCtx} → TmR Γ → RawTm Γ
  Raw-TmR = TmR.rawTmR

  Raw-SubR : ∀ {Γ Δ : RawCtx} → SubR Γ Δ → RawSub Γ Δ
  Raw-SubR = SubR.rawSubR

  TyR-wf : ∀ {Γ : RawCtx} → (A : TyR Γ) → Ty-iswf (Raw-TyR A)
  TyR-wf = TyR.ty-iswf

  TmR-wf : ∀ {Γ : RawCtx} → (t : TmR Γ) → Tm-iswf (Raw-TmR t)
  TmR-wf = TmR.tm-iswf

  SubR-wf : ∀ {Γ Δ : RawCtx} → (σ : SubR Γ Δ) → Sub-iswf (Raw-SubR σ)
  SubR-wf = SubR.sub-iswf

  -- Typing witnesses use the inductive raw typing relation.
  HasTyR : ∀ {Γ} → TmR Γ → TyR Γ → Set₁
  HasTyR t A = Raw.HasTy (Raw-TmR t) (Raw-TyR A)

  HasTySubR : ∀ {Γ Δ} → TmR Γ → TyR Δ → SubR Γ Δ → Set₁
  HasTySubR t A σ = Raw.HasTySub (Raw-TmR t) (Raw-TyR A) (Raw-SubR σ)

  data Ctx-iswf where
    ◆wf  : Ctx-iswf Raw.◆
    _▸wf_ : ∀ {Γ : RawCtx} → Ctx-iswf Γ → (A : TyR Γ) → Ctx-iswf (Γ Raw.▸ Raw-TyR A)

  data Ty-iswf where
    ⋆wf  : ∀ {Γ} → Ty-iswf {Γ} Raw.⋆
    hom-wf : ∀ {Γ} → (A : TyR Γ) → {t u : TmR Γ}
      → HasTyR t A → HasTyR u A
      → Ty-iswf (Raw.[ Raw-TyR A ] Raw-TmR t ⇒ Raw-TmR u)

  data Tm-iswf where
    var-wf : ∀ {Γ} → (x : RawVar Γ) → Tm-iswf (Raw.var x)
    coh-wf : ∀ {Γ Δ : RawCtx} {k : ℕ}
      → (ps  : P.IsPsCtx Δ k)
      → (wf  : Ctx-iswf Δ)
      → (A   : TyR Δ)
      → (u v : TmR Δ)
      → HasTyR u A
      → HasTyR v A
      → Full ps (Raw-TyR A) (Raw-TmR u) (Raw-TmR v)
      → (σ   : SubR Γ Δ)
      → Tm-iswf (Raw.coh (Raw-TyR A) (Raw-TmR u) (Raw-TmR v) (Raw-SubR σ))

  data Sub-iswf where
    ◆Swf : ∀ {Γ} → Sub-iswf {Γ} Raw.◆S
    ⟨_,_⟩:[_]wf : ∀ {Γ Δ : RawCtx} {A : TyR Δ}
      → (σ : SubR Γ Δ) → (t : TmR Γ)
      → HasTySubR t A σ
      → Sub-iswf (Raw.⟨_,_⟩ {A = Raw-TyR A} (Raw-SubR σ) (Raw-TmR t))
```

## Public Context Layer

The public `Ctx`, `Ty`, `Tm`, `Sub` records wrap their raw-indexed counterparts
and re-index over `Ctx`. The `cast-*` helpers convert between the two layers;
`HasTy` and `HasTySub` are the public typing-equality propositions.

```agda
record Ctx : Set₁ where
  pattern; constructor mkCtx; inductive
  field
    rawCtx  : RawCtx
    ctx-wf  : Ctx-iswf rawCtx

Raw-Ctx : Ctx → RawCtx
Raw-Ctx = Ctx.rawCtx

Ctx-wf : (Γ : Ctx) → Ctx-iswf (Raw-Ctx Γ)
Ctx-wf = Ctx.ctx-wf

record Ty (Γ : Ctx) : Set₁ where
  pattern
  constructor mkTy
  inductive
  field
    rawTy   : RawTy (Raw-Ctx Γ)
    ty-iswf : Ty-iswf rawTy

record Tm (Γ : Ctx) : Set₁ where
  pattern
  constructor mkTm
  inductive
  field
    rawTm   : RawTm (Raw-Ctx Γ)
    tm-iswf : Tm-iswf rawTm

record Sub (Γ Δ : Ctx) : Set₁ where
  pattern
  constructor mkSub
  inductive
  field
    rawSub   : RawSub (Raw-Ctx Γ) (Raw-Ctx Δ)
    sub-iswf : Sub-iswf rawSub

Raw-Ty : ∀ {Γ} → Ty Γ → RawTy (Raw-Ctx Γ)
Raw-Ty = Ty.rawTy

Ty-wf : ∀ {Γ} → (A : Ty Γ) → Ty-iswf (Raw-Ty A)
Ty-wf = Ty.ty-iswf

Raw-Tm : ∀ {Γ} → Tm Γ → RawTm (Raw-Ctx Γ)
Raw-Tm = Tm.rawTm

Tm-wf : ∀ {Γ} → (t : Tm Γ) → Tm-iswf (Raw-Tm t)
Tm-wf = Tm.tm-iswf

Raw-Sub : ∀ {Γ Δ} → Sub Γ Δ → RawSub (Raw-Ctx Γ) (Raw-Ctx Δ)
Raw-Sub = Sub.rawSub

Sub-wf : ∀ {Γ Δ} → (σ : Sub Γ Δ) → Sub-iswf (Raw-Sub σ)
Sub-wf = Sub.sub-iswf

-- Cast helpers: wrap public syntax as inner-layer records.
cast-ty : {Γ : Ctx} → Ty Γ → TyR (Raw-Ctx Γ)
cast-ty A = mkTyR (Raw-Ty A) (Ty-wf A)

cast-tm : {Γ : Ctx} → Tm Γ → TmR (Raw-Ctx Γ)
cast-tm t = mkTmR (Raw-Tm t) (Tm-wf t)

cast-sub : {Γ Δ : Ctx} → Sub Γ Δ → SubR (Raw-Ctx Γ) (Raw-Ctx Δ)
cast-sub σ = mkSubR (Raw-Sub σ) (Sub-wf σ)

-- Public typing witnesses.
HasTy : ∀ {Γ} → Tm Γ → Ty Γ → Set₁
HasTy t A = Raw.HasTy (Raw-Tm t) (Raw-Ty A)

HasTySub : ∀ {Γ Δ} → Tm Γ → Ty Δ → Sub Γ Δ → Set₁
HasTySub t A σ = Raw.HasTySub (Raw-Tm t) (Raw-Ty A) (Raw-Sub σ)
```

## Public Basic Constructors

The empty context `◆`, context extension `_▸_`, the object type `⋆`, and the
terminal substitution `◆S` are the basic building blocks. `Var Γ` is just
`RawVar (Raw-Ctx Γ)` — variables carry no well-formedness proof of their own.

```agda
Var : Ctx → Set₁
Var Γ = RawVar (Raw-Ctx Γ)

◆ : Ctx
◆ = mkCtx Raw.◆ ◆wf

_▸_ : (Γ : Ctx) → Ty Γ → Ctx
Γ ▸ A = mkCtx (Raw-Ctx Γ Raw.▸ Raw-Ty A) (Ctx-wf Γ ▸wf cast-ty A)

⋆ : ∀ {Γ} → Ty Γ
⋆ = mkTy Raw.⋆ ⋆wf

HasTyVar : ∀ {Γ} → Var Γ → Ty Γ → Set₁
HasTyVar x A = Raw.HasTyVar x (Raw-Ty A)

◆S : ∀ {Γ} → Sub Γ ◆
◆S = mkSub Raw.◆S ◆Swf
```

## Public Hom-Type, Snoc, and Coherence Constructors

These are the relation-native term/type/substitution constructors. The hom-type
and snoc-sub constructors take direct `HasTy` / `HasTySub` witnesses, so
well-formedness does not ask Agda to normalize `tyOf`. The `coh` constructor
packages the raw coherence with inductive endpoint typing witnesses and all
fullness data. Variable helpers `zero`, `succ`, `vz`, `vs`, and `var` complete
the relation-native term-level API. (Computed substitution `_[_]T` / `_[_]t` /
`_∘_` and `lookup` live in `2a-CaTT-Comp`.)

```agda
[_]_⇒_:[_,_] : {Γ : Ctx} → (A : Ty Γ) → (t u : Tm Γ)
  → HasTy t A → HasTy u A → Ty Γ
[ A ] t ⇒ u :[ p , q ] =
  mkTy (Raw.[ Raw-Ty A ] Raw-Tm t ⇒ Raw-Tm u)
    (hom-wf (cast-ty A) {cast-tm t} {cast-tm u} p q)

⟨_,_⟩:[_] : {Γ Δ : Ctx} → (σ : Sub Γ Δ) → {A : Ty Δ} → (t : Tm Γ)
  → HasTySub t A σ → Sub Γ (Δ ▸ A)
snocSubEq : {Γ Δ : Ctx} → (σ : Sub Γ Δ) → (A : Ty Δ) → (t : Tm Γ)
  → HasTySub t A σ → Sub Γ (Δ ▸ A)
snocSubEq (mkSub σ σwf) A t p =
  mkSub (Raw.⟨ σ , Raw-Tm t ⟩)
    (⟨_,_⟩:[_]wf {A = cast-ty A}
      (mkSubR σ σwf) (cast-tm t) p)

⟨_,_⟩:[_] = λ σ {A} t p → snocSubEq σ A t p

⟨_,_⟩∶[_] : {Γ Δ : Ctx} → (σ : Sub Γ Δ) → {A : Ty Δ} → (t : Tm Γ)
  → HasTySub t A σ → Sub Γ (Δ ▸ A)
snocSubJust : {Γ Δ : Ctx} → (σ : Sub Γ Δ) → (A : Ty Δ) → (t : Tm Γ)
  → HasTySub t A σ → Sub Γ (Δ ▸ A)
snocSubJust (mkSub σ σwf) A t p =
  mkSub (Raw.⟨ σ , Raw-Tm t ⟩)
    (⟨_,_⟩:[_]wf {A = cast-ty A}
      (mkSubR σ σwf) (cast-tm t) p)

⟨_,_⟩∶[_] = λ σ {A} t p → snocSubJust σ A t p

coh : ∀ {Γ Δ} {k : ℕ} → (ps : P.IsPsCtx (Raw-Ctx Δ) k) → (A : Ty Δ) → (u v : Tm Δ)
  → HasTy u A
  → HasTy v A
  → Full ps (Raw-Ty A) (Raw-Tm u) (Raw-Tm v)
  → (σ : Sub Γ Δ) → Tm Γ
coh {Γ} {Δ} ps A u v p q r σ =
  mkTm (Raw.coh (Raw-Ty A) (Raw-Tm u) (Raw-Tm v) (Raw-Sub σ))
    (coh-wf ps (Ctx-wf Δ) (cast-ty A) (cast-tm u) (cast-tm v)
             p q r
             (cast-sub σ))

zero : ∀ {Γ A} → Var (Γ ▸ A)
zero = Raw.zero

succ : ∀ {Γ A} → Var Γ → Var (Γ ▸ A)
succ = Raw.succ

vz : {Γ : Ctx} {A : Ty Γ} → Tm (Γ ▸ A)
vz = mkTm (Raw.var Raw.zero) (var-wf Raw.zero)

vs : {Γ : Ctx} {A : Ty Γ} → Var Γ → Tm (Γ ▸ A)
vs x = mkTm (Raw.var (Raw.succ x)) (var-wf (Raw.succ x))

var : ∀ {Γ} → Var Γ → Tm Γ
var x = mkTm (Raw.var x) (var-wf x)
```

## The identity-substitution recognizer

`IsIdSub b` recognizes `b : Sub Γ Γ` as an identity substitution, structurally: over
the empty context it is the terminal substitution `◆S`, and over an extended context
it is the snoc of a *weakened* identity base with the zero variable. The weakening is
the **relational** `Raw.WkSub` (we are in the core, so the computed `wkSub` / `idS`
are not available); this is exactly what lets downstream relational code refer to the
identity substitution without depending on the computed `idS`.

```agda
data IsIdSub : {Γ : Ctx} → Sub Γ Γ → Set₁ where
  id-◆ : IsIdSub {◆} ◆S
  id-▸ :
    {Γ : Ctx} {A : Ty Γ}
    {b : Sub Γ Γ} {bw : Sub (Γ ▸ A) Γ}
    (p : HasTySub (vz {A = A}) A bw) →
    IsIdSub b →
    Raw.WkSub (Raw-Sub b) (Raw-Sub bw) →
    IsIdSub (⟨ bw , vz {A = A} ⟩:[ p ])
```

## Context View

`CtxView` and `ctx-view` allow pattern matching on a well-formed context as
either `◆` or `Γ ▸ A`, recovering the pieces as typed CaTT objects rather than
raw data.

```agda
data CtxView : Ctx → Set₁ where
  ◆-view : CtxView ◆
  ▸-view : ∀ {Γ} (A : Ty Γ) → CtxView (Γ ▸ A)

ctx-view : (Γ : Ctx) → CtxView Γ
ctx-view (mkCtx Raw.◆ ◆wf) = ◆-view
ctx-view (mkCtx (_ Raw.▸ _) (Γwf ▸wf A0)) =
  ▸-view {Γ = mkCtx _ Γwf} (mkTy (Raw-TyR A0) (TyR-wf A0))
```

## Hom-types and relational typing helpers

`homTy` builds a typed hom-type from `HasTy` witnesses. The remaining lemmas are
relation-native typing transports. (Typed typing *uniqueness*, `hasTy-unique`,
lives in `2z-Extensionality`.)

```agda
-- Build a typed hom-type from HasTy witnesses.
homTy : {Γ : Ctx} → (A : Ty Γ) → (t u : Tm Γ) → HasTy t A → HasTy u A → Ty Γ
homTy A t u p q = [ A ] t ⇒ u :[ p , q ]

hasTy-conv : ∀ {Γ : Ctx} {t : Tm Γ} {A B : Ty Γ}
  → HasTy t A
  → A ≡ B
  → HasTy t B
hasTy-conv p refl = p

hasTy-tm-conv : ∀ {Γ : Ctx} {t u : Tm Γ} {A : Ty Γ}
  → t ≡ u
  → HasTy t A
  → HasTy u A
hasTy-tm-conv refl p = p

-- Transport a typing equality across a context equality.
-- This is the generic version of the context casts that appear later in 2b.
ctx-subst-hasTy : ∀ {Δ Δ' : Ctx} → (e : Δ ≡ Δ') → {t : Tm Δ} → {A : Ty Δ}
  → HasTy t A → HasTy (subst Tm e t) (subst Ty e A)
ctx-subst-hasTy refl p = p

castSub : ∀ {Γ Δ Δ'} → Δ ≡ Δ' → Sub Γ Δ → Sub Γ Δ'
castSub {Γ} e σ = subst (Sub Γ) e σ

HasTySub-castSub : ∀ {Γ Δ Δ'} (e : Δ ≡ Δ') {t : Tm Γ} {A : Ty Δ} {σ : Sub Γ Δ}
  → HasTySub t A σ → HasTySub t (subst Ty e A) (castSub e σ)
HasTySub-castSub refl p = p

-- The codomain of a well-formed substitution is a well-formed context.
sub-cod-iswf : ∀ {Γ Δ} (σ : RawSub Γ Δ) → Sub-iswf σ → Ctx-iswf Δ
sub-cod-iswf Raw.◆S ◆Swf = ◆wf
sub-cod-iswf (Raw.⟨ σ , t ⟩) (⟨_,_⟩:[_]wf {A = A} (mkSubR .σ σwf) (mkTmR .t twf) p) =
  sub-cod-iswf σ σwf ▸wf A
```

## Typed pasting / dimension aliases

Typed aliases for the relational pasting/dimension API of `1c-Pasting`.
These unfold definitionally to their raw counterparts, so the raw
constructors and lemmas (`P.isps-ob`, `P.dangling-*`, …) may be used directly
where a typed witness is expected. Dimension-facing code should stay on these
relations; the computed extension-cell builders `hom-type-ext` / `ext-ctx` live
in `2a-CaTT-Comp`.

```agda
HasDimTy : ∀ {Γ} → Ty Γ → ℕ → Set₁
HasDimTy A n = P.HasDimTy (Raw-Ty A) n

HasDimCtx : Ctx → ℕ → Set₁
HasDimCtx Γ n = P.HasDimCtx (Raw-Ctx Γ) n

-- Note: there is no typed `HasDimVar` alias. A typed variable `x : Var Γ` is
-- already a raw variable, so `P.HasDimVar x n` applies directly; a typed alias
-- would only introduce a phantom `Γ` index that Agda cannot solve.

IsPsCtx : Ctx → ℕ → Set₁
IsPsCtx Γ k = P.IsPsCtx (Raw-Ctx Γ) k

IsDangling : ∀ {Γ k} → IsPsCtx Γ k → Var Γ → Ty Γ → ℕ → Set₁
IsDangling Γps x A n = P.IsDangling Γps x (Raw-Ty A) n

-- The relational constructors `P.isps-ob`, `P.isps-ext`, `P.dangling-ob`,
-- `P.dangling-f`, `P.dangling-y`, `P.dangling-weak` are used directly: their
-- raw signatures already coincide (definitionally) with the typed aliases, and
-- a typed-signature wrapper cannot recover the typed `Γ`/`A` indices from the
-- raw witness (`Raw-Ctx` / `Raw-Ty` are not injective).

-- Typed wrappers for the positive structural lemmas.
isDangling-hasTyVar : ∀ {Γ : Ctx} {k : ℕ} {Γps : IsPsCtx Γ k}
  {x : Var Γ} {A : Ty Γ} {n : ℕ} →
  IsDangling Γps x A n → HasTy (var x) A
isDangling-hasTyVar d = Raw.varTy (P.isDangling-hasTyVar d)

isDangling-hasDimTy : ∀ {Γ : Ctx} {k : ℕ} {Γps : IsPsCtx Γ k}
  {x : Var Γ} {A : Ty Γ} {n : ℕ} →
  IsDangling Γps x A n → HasDimTy A n
isDangling-hasDimTy d = P.isDangling-hasDimTy d

isDangling-hasDimVar : ∀ {Γ : Ctx} {k : ℕ} {Γps : IsPsCtx Γ k}
  {x : Var Γ} {A : Ty Γ} {n : ℕ} →
  IsDangling Γps x A n → P.HasDimVar x n
isDangling-hasDimVar d = P.isDangling-hasDimVar d

isPsCtx-hasDimCtx : ∀ {Γ : Ctx} {k : ℕ} → IsPsCtx Γ k → HasDimCtx Γ k
isPsCtx-hasDimCtx Γps = P.isPsCtx-hasDimCtx Γps

isDangling≤ctx : ∀ {Γ : Ctx} {k : ℕ} {Γps : IsPsCtx Γ k}
  {x : Var Γ} {A : Ty Γ} {n : ℕ} →
  IsDangling Γps x A n → n ≤ k
isDangling≤ctx d = P.isDangling≤ctx d
```

## An API for well-typed terms

```agda
record TmTyped {Γ : Ctx} (A : Ty Γ) : Set₁ where
  pattern
  constructor mk
  field
    tm : Tm Γ
    tp : HasTy tm A

MorTy : {Γ : Ctx} {A : Ty Γ} → (a b : TmTyped A) → Ty Γ
MorTy {Γ} {A} (mk tma tpa) (mk tmb tpb) =
  homTy A tma tmb tpa tpb

MorTm : {Γ : Ctx} {A : Ty Γ} → (a b : TmTyped A) → Set₁
MorTm a b = TmTyped (MorTy a b)
```

## Extensionality

The well-formedness **UIP** proofs (`uip`, `Ctx-iswf-uip`, `Ty-iswf-uip`,
`Tm-iswf-uip`, `Sub-iswf-uip`, and the `Full-uip` postulate) and the
**extensionality** lemmas (`Ty-ext`, `Tm-ext`, `Sub-ext`) now live in the
companion module `2z-Extensionality`, together with the typed `hasTy-unique`.
