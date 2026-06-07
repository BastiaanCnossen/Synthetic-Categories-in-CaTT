# 2a-CaTT-Comp: Computed Typed CaTT Operations

This module is the computational companion to `2a-CaTT`. The relational core
(`2a-CaTT`) holds the proposition-facing material: the intrinsic well-formedness
relations (`Ctx-iswf`, `Ty-iswf`, `Tm-iswf`, `Sub-iswf`), the proof-carrying
records, the public `Ctx`/`Ty`/`Tm`/`Sub` layer, the relational typing witnesses
`HasTy`/`HasTySub`, the relation-native constructors (`[_]_⇒_:[_,_]`, `homTy`,
`coh`, the snoc-substitution constructors, the variable terms), and the typed
wrappers for the relational pasting/dimension API. The extensionality/UIP
infrastructure (`*-iswf-uip`, `Ty-ext`/`Tm-ext`/`Sub-ext`, `Full-uip`,
`hasTy-unique`) lives in `2z-Extensionality`. All of these import only the
relational `1-preCaTT` cores.

This module re-exports that core (and `2z-Extensionality`) and then adds
everything that genuinely needs a *computed* raw operation or a computed
compatibility bridge:

- the inner-layer structural operations (`_[_]TR`, `_[_]tR`, `_∘R_`, and their
  well-formedness proofs `hasTy-lookup`, `hasTy-sub`, `∘R-iswf-raw`, …) whose
  types mention `Raw._[_]T` / `Raw._[_]t` / `Raw._∘_`;
- the public computed substitution/composition (`_[_]T`, `_[_]t`, `_∘_`),
  weakening (`wkTy`, `wkTm`, `wkSub`, `wk`), identity (`idS`), `lookup`, the type
  inference functions `var-to-type` / `tyOf`, and the canonical typing witnesses
  `var-hasTy` / `vz-hasTy` / `vs-hasTy`;
- the computed equational theory (`[]T-∘`, `∘-assoc`, `wkTy-[]T′`, …) and the
  `tyOf` ↔ `HasTy` compatibility bridges (`HasTy→tyOf≡`, `tyOf≡→HasTy`, …);
- the extension-cell builders (`hom-type-ext`, `ext-ctx`) whose types mention
  computed `wkTy`.

Import `2a-CaTT` when only the relational API is needed; import this module when a
construction genuinely consumes a computed output.

```agda
module 2a-CaTT-Comp where

open import 2a-CaTT public
open import 2z-Extensionality public
import 1a-RawSyntax-Comp as Raw
import 1b-Dependency as Dep

open import Data.Nat using (ℕ; suc; _⊔_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂; subst)

module D = Dep

open Raw using (RawCtx; RawTy; RawTm; RawSub; RawVar)

infixl 8 _[_]T _[_]t
infixr 10 _∘_
```

## Inner Raw-Indexed Operations

These are the structural operations on the raw-indexed records `TyR`/`TmR`/`SubR`
together with their well-formedness proofs. Their types mention the computed raw
operations `Raw._[_]T`, `Raw._[_]t`, and `Raw._∘_`, so they live here rather than
in the relational core. The block also retains the legacy `tyOf` equality bridges
(`tyOf-lookup-comm`, `tyOf-comm`).

```agda
mutual
  -- Forward declarations for operations defined below.
  []TR-iswf : ∀ {Γ Δ} → (A : TyR Δ) → (σ : SubR Γ Δ)
    → Ty-iswf (Raw-TyR A Raw.[ Raw-SubR σ ]T)
  _[_]TR   : ∀ {Γ Δ} → TyR Δ → SubR Γ Δ → TyR Γ

  []tR-iswf : ∀ {Γ Δ} → (t : TmR Δ) → (σ : SubR Γ Δ)
    → Tm-iswf (Raw-TmR t Raw.[ Raw-SubR σ ]t)
  _[_]tR   : ∀ {Γ Δ} → TmR Δ → SubR Γ Δ → TmR Γ

  _∘R_     : ∀ {Γ Δ Θ} → SubR Δ Θ → SubR Γ Δ → SubR Γ Θ

  -- The inductive typing relation is stable under lookup and substitution.
  hasTy-lookup :
    ∀ {Γ Δ : RawCtx} {x : RawVar Δ} {A : RawTy Δ}
    → Raw.HasTyVar x A
    → (σ : SubR Γ Δ)
    → Raw.HasTy (Raw.lookup x (Raw-SubR σ)) (A Raw.[ Raw-SubR σ ]T)
  hasTy-lookup (Raw.zeroTy q)
    (mkSubR _ (⟨_,_⟩:[_]wf {A = A} σ t p)) =
      subst (Raw.HasTy (Raw-TmR t))
        (sym (Raw.wkTy-rel-[]T q (Raw-SubR σ) (Raw-TmR t)))
        (Raw.hasTySub→computed p)
  hasTy-lookup (Raw.succTy {x = x} p q)
    (mkSubR _ (⟨_,_⟩:[_]wf σ t _)) =
      subst (Raw.HasTy (Raw.lookup x (Raw-SubR σ)))
        (sym (Raw.wkTy-rel-[]T q (Raw-SubR σ) (Raw-TmR t)))
        (hasTy-lookup p σ)

  hasTy-sub :
    ∀ {Γ Δ : RawCtx} {t : RawTm Δ} {A : RawTy Δ}
    → Raw.HasTy t A
    → (σ : SubR Γ Δ)
    → Raw.HasTy (t Raw.[ Raw-SubR σ ]t) (A Raw.[ Raw-SubR σ ]T)
  hasTy-sub (Raw.varTy p) σ = hasTy-lookup p σ
  hasTy-sub (Raw.cohTy {A = A} {u = u} {v = v} {σ = τ} p) σ =
    Raw.cohTy
      (subst (Raw.SubstTy (Raw.[ A ] u ⇒ v) (τ Raw.∘ Raw-SubR σ))
        (trans (Raw.[∘]T (Raw.[ A ] u ⇒ v) τ (Raw-SubR σ))
               (cong (λ C → C Raw.[ Raw-SubR σ ]T) (Raw.substTy→[]T≡ p)))
        (Raw.substTy (Raw.[ A ] u ⇒ v) (τ Raw.∘ Raw-SubR σ)))

  -- Legacy equality bridges for constructions that still need a canonical type.
  tyOf-lookup-comm :
    ∀ {Γ Δ : RawCtx} (x : RawVar Δ) (σ : SubR Γ Δ)
    → Raw.tyOf (Raw.lookup x (Raw-SubR σ))
        ≡ Raw.var-to-type x Raw.[ Raw-SubR σ ]T
  tyOf-lookup-comm x σ = Raw.hasTy→tyOf (hasTy-lookup (Raw.hasTyVar x) σ)

  tyOf-comm :
    ∀ {Γ Δ : RawCtx} (t : RawTm Δ) (A : RawTy Δ) (σ : SubR Γ Δ)
    → Raw.tyOf t ≡ A
    → Raw.tyOf (t Raw.[ Raw-SubR σ ]t) ≡ A Raw.[ Raw-SubR σ ]T
  tyOf-comm t A σ p =
    Raw.hasTy→tyOf
      (hasTy-sub {t = t} {A = A} (Raw.tyOf≡→hasTy {t = t} {A = A} p) σ)

  -- Composition preserves well-formedness.
  ∘R-iswf-raw :
    ∀ {Γ Δ Θ : RawCtx} {τ : RawSub Δ Θ}
    → Sub-iswf τ → (σ : SubR Γ Δ)
    → Sub-iswf (τ Raw.∘ Raw-SubR σ)
  ∘R-iswf-raw {τ = Raw.◆S} ◆Swf σ = ◆Swf
  ∘R-iswf-raw
    (⟨_,_⟩:[_]wf {A = A} (mkSubR τ τwf) (mkTmR t twf) r)
    (mkSubR σ σwf) =
      ⟨_,_⟩:[_]wf {A = A}
        (mkSubR
          (τ Raw.∘ Raw-SubR (mkSubR σ σwf))
          (∘R-iswf-raw τwf (mkSubR σ σwf)))
        (mkTmR
          (t Raw.[ Raw-SubR (mkSubR σ σwf) ]t)
          ([]tR-iswf-raw twf (mkSubR σ σwf)))
        (Raw.computed-hasTySub
          (subst (Raw.HasTy (t Raw.[ σ ]t))
            (sym (Raw.[∘]T (Raw-TyR A) τ σ))
            (hasTy-sub (Raw.hasTySub→computed r) (mkSubR σ σwf))))

  mkSubR τ τwf ∘R mkSubR σ σwf =
    mkSubR (τ Raw.∘ σ) (∘R-iswf-raw τwf (mkSubR σ σwf))

  -- Type substitution preserves well-formedness.
  []TR-iswf-raw :
    ∀ {Γ Δ : RawCtx} (A : RawTy Δ) → Ty-iswf A → (σ : SubR Γ Δ)
    → Ty-iswf (A Raw.[ Raw-SubR σ ]T)
  []TR-iswf-raw Raw.⋆ ⋆wf σ = ⋆wf
  []TR-iswf-raw (Raw.[ A ] t ⇒ u)
    (hom-wf (mkTyR .A Awf) {mkTmR .t twf} {mkTmR .u uwf} p q)
    (mkSubR σ σwf) =
      hom-wf
        (mkTyR (A Raw.[ σ ]T) ([]TR-iswf-raw A Awf (mkSubR σ σwf)))
        {mkTmR (t Raw.[ σ ]t) ([]tR-iswf (mkTmR t twf) (mkSubR σ σwf))}
        {mkTmR (u Raw.[ σ ]t) ([]tR-iswf (mkTmR u uwf) (mkSubR σ σwf))}
        (hasTy-sub p (mkSubR σ σwf))
        (hasTy-sub q (mkSubR σ σwf))

  []TR-iswf A σ = []TR-iswf-raw (Raw-TyR A) (TyR-wf A) σ

  A [ σ ]TR = mkTyR (Raw-TyR A Raw.[ Raw-SubR σ ]T) ([]TR-iswf A σ)

  -- Term substitution preserves well-formedness.
  lookup-R-iswf : ∀ {Γ Δ} (x : RawVar Δ) (σ : SubR Γ Δ)
    → Tm-iswf (Raw.lookup x (Raw-SubR σ))
  lookup-R-iswf Raw.zero
    (mkSubR _ (⟨_,_⟩:[_]wf _ (mkTmR _ twf) _)) = twf
  lookup-R-iswf (Raw.succ x)
    (mkSubR _ (⟨_,_⟩:[_]wf σ _ _)) =
      lookup-R-iswf x σ

  []tR-iswf-raw :
    ∀ {Γ Δ : RawCtx} {t : RawTm Δ}
    → Tm-iswf t → (σ : SubR Γ Δ)
    → Tm-iswf (t Raw.[ Raw-SubR σ ]t)
  []tR-iswf-raw (var-wf x) σ = lookup-R-iswf x σ
  []tR-iswf-raw
    (coh-wf ps Δwf A u v p q r (mkSubR γ γwf))
    (mkSubR σ σwf) =
      coh-wf ps Δwf A u v p q r
        (mkSubR (γ Raw.∘ σ) (∘R-iswf-raw γwf (mkSubR σ σwf)))

  []tR-iswf t σ = []tR-iswf-raw (TmR-wf t) σ

  t [ σ ]tR = mkTmR (Raw-TmR t Raw.[ Raw-SubR σ ]t) ([]tR-iswf t σ)
```

## Weakening lemmas

`hasTy-wk` transports an inductive typing witness through raw weakening.
`tyOf-wk` retains the corresponding equality bridge for legacy constructions.

```agda
hasTy-wk :
  ∀ {Γ : RawCtx} {B : RawTy Γ} {t : RawTm Γ} {A : RawTy Γ}
  → Raw.HasTy t A
  → Raw.HasTy (Raw.wkTm {A = B} t) (Raw.wkTy {A = B} A)
hasTy-wk = Raw.hasTy-wk

-- Raw type-of commutes with weakening.
-- For var and coh it reduces to definitional equality or wkTy-[]T-r.
tyOf-wk :
  ∀ {Γ : RawCtx} {B : RawTy Γ} {A : RawTy Γ}
  → (t : RawTm Γ)
  → Raw.tyOf t ≡ A
  → Raw.tyOf (Raw.wkTm {A = B} t) ≡ Raw.wkTy {A = B} A
tyOf-wk (Raw.var x) refl = refl
tyOf-wk (Raw.coh C u v σ) refl =
  sym (Raw.wkTy-[]T-r (Raw.[ C ] u ⇒ v) σ)
```

## Weakening

`wkTm` and `wkSub` weaken a typed term or substitution by a new type `A`,
landing in the extended context `Γ ▸ A`. `wkTy-iswf-raw` does the same for
raw well-formed types. The `wkTm-iswf` / `wkSub-iswf-raw` pair is mutually
recursive because a weakened coherence contains a weakened substitution, which
in turn may contain weakened terms.

```agda
-- wkTm-iswf and wkSub-iswf-raw are mutually recursive.
mutual
  wkTm-iswf :
    ∀ {Γ : RawCtx} {B : RawTy Γ} → (t : TmR Γ)
    → Tm-iswf (Raw.wkTm {A = B} (Raw-TmR t))
  wkTm-iswf (mkTmR (Raw.var x) (var-wf .x)) = var-wf (Raw.succ x)
  wkTm-iswf {B = B} (mkTmR (Raw.coh A u v σ)
    (coh-wf ps Δwf tA tu tv p q r (mkSubR σ σwf))) =
      coh-wf ps Δwf tA tu tv p q r
        (mkSubR (Raw.wkSub {A = B} σ)
                (wkSub-iswf-raw {B = B} σ σwf))

  wkSub-iswf-raw :
    ∀ {Γ Δ : RawCtx} {B : RawTy Γ}
    → (σ : RawSub Γ Δ) → Sub-iswf σ
    → Sub-iswf (Raw.wkSub {A = B} σ)
  wkSub-iswf-raw Raw.◆S        ◆Swf = ◆Swf
  wkSub-iswf-raw (Raw.⟨ σ , t ⟩)
    (⟨_,_⟩:[_]wf {A = A} (mkSubR .σ σwf) (mkTmR .t twf) r) =
      ⟨_,_⟩:[_]wf {A = A}
        (mkSubR (Raw.wkSub σ)
                (wkSub-iswf-raw σ σwf))
        (mkTmR (Raw.wkTm t) (wkTm-iswf (mkTmR t twf)))
        (Raw.hasTySub-wkSub r)

wkTy-iswf-raw :
  ∀ {Γ : RawCtx} {B : RawTy Γ}
  → (A : RawTy Γ) → Ty-iswf A
  → Ty-iswf (Raw.wkTy {A = B} A)
wkTy-iswf-raw Raw.⋆ ⋆wf = ⋆wf
wkTy-iswf-raw {B = B} (Raw.[ A ] t ⇒ u)
  (hom-wf (mkTyR .A Awf) {mkTmR .t twf} {mkTmR .u uwf} p q) =
    hom-wf
      (mkTyR (Raw.wkTy A) (wkTy-iswf-raw A Awf))
      {mkTmR (Raw.wkTm t) (wkTm-iswf (mkTmR t twf))}
      {mkTmR (Raw.wkTm u) (wkTm-iswf (mkTmR u uwf))}
      (hasTy-wk p)
      (hasTy-wk q)

wkTy : ∀ {Γ} {A : Ty Γ} → Ty Γ → Ty (Γ ▸ A)
wkTy {A = A} B =
  mkTy (Raw.wkTy {A = Raw-Ty A} (Raw-Ty B))
       (wkTy-iswf-raw (Raw-Ty B) (Ty-wf B))

wkTm : ∀ {Γ} {A : Ty Γ} → Tm Γ → Tm (Γ ▸ A)
wkTm {A = A} t =
  mkTm (Raw.wkTm {A = Raw-Ty A} (Raw-Tm t))
       (wkTm-iswf {B = Raw-Ty A} (cast-tm t))

wkSub : ∀ {Γ Δ} {A : Ty Γ} → Sub Γ Δ → Sub (Γ ▸ A) Δ
wkSub {A = A} σ =
  mkSub (Raw.wkSub {A = Raw-Ty A} (Raw-Sub σ))
        (wkSub-iswf-raw {B = Raw-Ty A} (Raw-Sub σ) (Sub-wf σ))
```

## var-to-type and tyOf

`var-to-type x` lifts `x` to a typed term's type by reading off the raw
`var-to-type` and proving well-formedness by induction on the context. `tyOf t`
computes the type of a typed term by destructuring the `Tm-iswf` witness:
variables give `var-to-type`, coherences give the substituted hom-type.
`tyOf-from-tyOf` relates the raw and typed type-of functions.

```agda
var-to-type-iswf' :
  ∀ (Γ : RawCtx) → Ctx-iswf Γ → (x : RawVar Γ)
  → Ty-iswf (Raw.var-to-type x)
var-to-type-iswf' Raw.◆        ◆wf         ()
var-to-type-iswf' (_ Raw.▸ _) (Γwf ▸wf A0) Raw.zero =
  wkTy-iswf-raw (Raw-TyR A0) (TyR-wf A0)
var-to-type-iswf' (_ Raw.▸ _) (Γwf ▸wf A0) (Raw.succ x) =
  wkTy-iswf-raw (Raw.var-to-type x) (var-to-type-iswf' _ Γwf x)

var-to-type-iswf : {Γ : Ctx} → (x : Var Γ) → Ty-iswf (Raw.var-to-type x)
var-to-type-iswf {Γ} x = var-to-type-iswf' (Raw-Ctx Γ) (Ctx-wf Γ) x

var-to-type : ∀ {Γ} → Var Γ → Ty Γ
var-to-type {Γ} x = mkTy (Raw.var-to-type x) (var-to-type-iswf {Γ} x)

-- tyOf by pattern matching on the Tm-iswf witness.
tyOf : ∀ {Γ} → Tm Γ → Ty Γ
tyOf {Γ} (mkTm (Raw.var x) (var-wf .x)) =
  mkTy (Raw.var-to-type x) (var-to-type-iswf {Γ = Γ} x)
tyOf (mkTm (Raw.coh _ _ _ _) (coh-wf _ _ A u v p q r σR)) =
  mkTy ((Raw.[ Raw-TyR A ] Raw-TmR u ⇒ Raw-TmR v) Raw.[ Raw-SubR σR ]T)
       ([]TR-iswf (mkTyR (Raw.[ Raw-TyR A ] Raw-TmR u ⇒ Raw-TmR v)
                          (hom-wf A {t = u} {u = v} p q))
                 σR)

tyOf-from-tyOf : ∀ {Γ} (t : Tm Γ) → Raw.tyOf (Raw-Tm t) ≡ Raw-Ty (tyOf t)
tyOf-from-tyOf (mkTm (Raw.var x) (var-wf .x)) = refl
tyOf-from-tyOf (mkTm (Raw.coh _ _ _ _) (coh-wf _ _ A u v p q r σR)) = refl
```

## Public Computed Substitution and Composition

The public API for substitution (`_[_]T`, `_[_]t`, `_∘_`) wraps the inner-layer
operations. The variable helpers `lookup`, and the canonical typing witnesses
`var-hasTy` / `vz-hasTy` / `vs-hasTy`, complete the computed term-level API.

```agda
_[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
A [ σ ]T = mkTy (Raw-Ty A Raw.[ Raw-Sub σ ]T)
                ([]TR-iswf (cast-ty A) (cast-sub σ))

_[_]t : ∀ {Γ Δ} → Tm Δ → Sub Γ Δ → Tm Γ
t [ σ ]t = mkTm (Raw-Tm t Raw.[ Raw-Sub σ ]t)
                ([]tR-iswf (cast-tm t) (cast-sub σ))

_∘_ : ∀ {Γ Δ Θ} → Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
τ ∘ σ = mkSub (Raw-Sub τ Raw.∘ Raw-Sub σ)
              (∘R-iswf-raw (Sub-wf τ) (cast-sub σ))

var-hasTy : ∀ {Γ : Ctx} → (x : Var Γ)
  → HasTy (var {Γ = Γ} x) (var-to-type {Γ = Γ} x)
var-hasTy x = Raw.varTy (Raw.hasTyVar x)

vz-hasTy : ∀ {Γ} {A : Ty Γ} → HasTy (vz {A = A}) (wkTy A)
vz-hasTy = Raw.varTy (Raw.zeroTy (Raw.wkTy-rel _))

vs-hasTy : ∀ {Γ} {A : Ty Γ} → (x : Var Γ)
  → HasTy (vs {A = A} x) (wkTy (var-to-type x))
vs-hasTy x = Raw.varTy (Raw.succTy (Raw.hasTyVar x) (Raw.wkTy-rel _))

lookup-iswf : ∀ {Γ Δ : RawCtx} (x : RawVar Δ) (σ : SubR Γ Δ)
  → Tm-iswf (Raw.lookup x (Raw-SubR σ))
lookup-iswf x σ = lookup-R-iswf x σ

lookup : ∀ {Γ Δ} → Var Δ → Sub Γ Δ → Tm Γ
lookup x σ = mkTm (Raw.lookup x (Raw-Sub σ))
                  (lookup-R-iswf x (cast-sub σ))
```

## Identity and Canonical Weakening

`idS Γ` is the identity substitution, constructed by induction on the context:
the empty case is `◆S`; the extension case snocs the identity on `Γ'` (weakened
by `A`) with the fresh variable `vz`. `wk` is the canonical weakening
substitution `idS Γ` weakened by `A`, mapping `Γ ▸ A` back to `Γ`.

```agda
mutual
  idS : (Γ : Ctx) → Sub Γ Γ
  idS-iswf : (Γ : Ctx) → Sub-iswf (Raw.idS (Raw-Ctx Γ))

  idS Γ = mkSub (Raw.idS (Raw-Ctx Γ)) (idS-iswf Γ)

  idS-iswf (mkCtx Raw.◆ ◆wf) = ◆Swf
  idS-iswf (mkCtx (_ Raw.▸ _) (Γwf ▸wf A0)) =
    let
      Γ' : Ctx
      Γ' = mkCtx _ Γwf
      A' : Ty Γ'
      A' = mkTy (Raw-TyR A0) (TyR-wf A0)
    in
    ⟨_,_⟩:[_]wf {A = cast-ty A'}
      (cast-sub (wkSub {A = A'} (idS Γ')))
      (cast-tm (vz {A = A'}))
      (Raw.computed-hasTySub
        (subst (Raw.HasTy (Raw.var Raw.zero))
          (trans
            (sym (cong Raw.wkTy (Raw.[idS]T (Raw-Ty A'))))
            (Raw.wkTy-[]T-r (Raw-Ty A') (Raw.idS (Raw-Ctx Γ'))))
          (Raw.varTy (Raw.zeroTy (Raw.wkTy-rel _)))))

wk : ∀ {Γ} {A : Ty Γ} → Sub (Γ ▸ A) Γ
wk {Γ} {A} = wkSub {A = A} (idS Γ)
```

## Computed Hom-type / tyOf Bridges

`Raw-Ty-Sub` records that the typed substitution agrees with the raw one;
`HasTy→tyOf≡` and `tyOf≡→HasTy` convert between the relational `HasTy` form and
the legacy `tyOf` equality form.

```agda
-- Passage to raw commutes with substitution
Raw-Ty-Sub : ∀ {Γ Δ} (A : Ty Δ) (σ : Sub Γ Δ)
  → Raw-Ty (A [ σ ]T) ≡ Raw-Ty A Raw.[ Raw-Sub σ ]T
Raw-Ty-Sub A σ = refl

-- Convert between the raw `tyOf` equality and the typed `tyOf` equality forms.
HasTy→tyOf≡ : ∀ {Γ} {t : Tm Γ} {A : Ty Γ}
  → HasTy t A → tyOf t ≡ A
HasTy→tyOf≡ {t = t} p =
  Ty-ext (trans (sym (tyOf-from-tyOf t)) (Raw.hasTy→tyOf p))

tyOf≡→HasTy : ∀ {Γ} {t : Tm Γ} {A : Ty Γ}
  → tyOf t ≡ A → HasTy t A
tyOf≡→HasTy {t = t} p =
  Raw.tyOf≡→hasTy (trans (tyOf-from-tyOf t) (cong Raw-Ty p))
```

## Derived Computed Helpers

This section collects the computed equational theory and the substitution
helpers consumed by downstream files.

```agda
[]T-id : {Γ : Ctx} (A : Ty Γ) → A [ idS Γ ]T ≡ A
[]T-id A = Ty-ext (Raw.[idS]T (Raw-Ty A))

[]t-id : {Γ : Ctx} (t : Tm Γ) → t [ idS Γ ]t ≡ t
[]t-id t = Tm-ext (Raw.[idS]t (Raw-Tm t))

raw-∘-idS-l :
  ∀ {Γ Δ : RawCtx}
  → (σ : RawSub Γ Δ)
  → Raw.idS Δ Raw.∘ σ ≡ σ
raw-∘-idS-l Raw.◆S = refl
raw-∘-idS-l (Raw.⟨ σ , t ⟩) =
  cong₂ Raw.⟨_,_⟩
    (trans (Raw.wkSub-∘ (Raw.idS _) σ t) (raw-∘-idS-l σ))
    refl

∘-idS-l :
  ∀ {Γ Δ : Ctx}
  → (σ : Sub Γ Δ)
  → idS Δ ∘ σ ≡ σ
∘-idS-l σ = Sub-ext (raw-∘-idS-l (Raw-Sub σ))

∘-idS-r :
  ∀ {Γ Δ : Ctx}
  → (σ : Sub Γ Δ)
  → σ ∘ idS Γ ≡ σ
∘-idS-r σ = Sub-ext (Raw.∘-idS-r (Raw-Sub σ))

[]t-∘ :
  ∀ {Γ Δ Θ : Ctx} {t : Tm Θ} {τ : Sub Δ Θ} {σ : Sub Γ Δ}
  → (t [ τ ]t) [ σ ]t ≡ t [ τ ∘ σ ]t
[]t-∘ {t = t} {τ = τ} {σ = σ} =
  Tm-ext (sym (Raw.[∘]t (Raw-Tm t) (Raw-Sub τ) (Raw-Sub σ)))

[]T-∘ :
  ∀ {Γ Δ Θ : Ctx} {A : Ty Θ} {τ : Sub Δ Θ} {σ : Sub Γ Δ}
  → (A [ τ ]T) [ σ ]T ≡ A [ τ ∘ σ ]T
[]T-∘ {A = A} {τ = τ} {σ = σ} =
  Ty-ext (sym (Raw.[∘]T (Raw-Ty A) (Raw-Sub τ) (Raw-Sub σ)))

∘-assoc : ∀ {Γ Δ Θ Ξ : Ctx}
  → (γ : Sub Θ Ξ)
  → (τ : Sub Δ Θ)
  → (σ : Sub Γ Δ)
  → γ ∘ (τ ∘ σ) ≡ (γ ∘ τ) ∘ σ
∘-assoc γ τ σ = Sub-ext (Raw.assocS (Raw-Sub γ) (Raw-Sub τ) (Raw-Sub σ))
```

The migration uses the raw adapters of 1a directly (`Raw.hasTySub→computed`
/ `Raw.computed-hasTySub`). Their implicits are raw, so they are inferred
from the raw components of the public `HasTySub` / `HasTy` types; a
typed-level wrapper would forget those through the non-injective `Raw-Ty` /
`Raw-Sub` and leave unsolved metas at call sites. These are migration
ergonomics only — prefer relational `HasTySub` construction where possible.

```agda
hasTySub-conv : ∀ {Γ Δ Θ : Ctx} {t : Tm Γ}
  {A : Ty Δ} {B : Ty Θ} {σ : Sub Γ Δ} {τ : Sub Γ Θ}
  → HasTySub t A σ
  → A [ σ ]T ≡ B [ τ ]T
  → HasTySub t B τ
hasTySub-conv {t = t} p e =
  Raw.computed-hasTySub (subst (HasTy t) e (Raw.hasTySub→computed p))

tmSub-typed : ∀ {Γ Δ} {t : Tm Δ} {A : Ty Δ} {σ : Sub Γ Δ}
  → HasTy t A → HasTy (t [ σ ]t) (A [ σ ]T)
tmSub-typed {t = t} {A = A} {σ = σ} p =
  hasTy-sub p (cast-sub σ)

hasTySub-sub : ∀ {Γ Δ Θ} {t : Tm Δ} {A : Ty Θ}
  {τ : Sub Δ Θ} {σ : Sub Γ Δ}
  → HasTySub t A τ
  → HasTySub (t [ σ ]t) A (τ ∘ σ)
hasTySub-sub {t = t} {A = A} {τ = τ} {σ = σ} p =
  Raw.computed-hasTySub
    (hasTy-conv
      {t = t [ σ ]t}
      {A = (A [ τ ]T) [ σ ]T}
      {B = A [ τ ∘ σ ]T}
      (tmSub-typed {t = t} {A = A [ τ ]T} {σ = σ} (Raw.hasTySub→computed p))
      ([]T-∘ {A = A} {τ = τ} {σ = σ}))

tyOfSub : {Γ Δ : Ctx} {t : Tm Δ} {A : Ty Δ} {σ : Sub Γ Δ}
  → tyOf t ≡ A → tyOf (t [ σ ]t) ≡ A [ σ ]T
tyOfSub {t = t} {A = A} {σ = σ} p =
  Ty-ext
    (trans (sym (tyOf-from-tyOf (t [ σ ]t)))
      (trans (tyOf-comm (Raw-Tm t) (Raw-Ty A) (cast-sub σ)
        (trans (tyOf-from-tyOf t) (cong Raw-Ty p)))
          (sym (Raw-Ty-Sub A σ))))

lookup-raw : ∀ {Γ Δ} (x : Var Δ)
  → {σraw : RawSub (Raw-Ctx Γ) (Raw-Ctx Δ)} → (σwf : Sub-iswf σraw)
  → {t : Tm Γ} → Raw.lookup x σraw ≡ Raw-Tm t
  → lookup x (mkSub {Γ = Γ} {Δ = Δ} σraw σwf) ≡ t
lookup-raw x σwf p = Tm-ext p

lookup-castSub : ∀ {Γ Δ Δ'} (e : Δ ≡ Δ') (x : Var Δ) (σ : Sub Γ Δ)
  → lookup (subst Var e x) (castSub e σ) ≡ lookup x σ
lookup-castSub refl x σ = refl

wkTm-raw : ∀ {Γ} {A : Ty Γ} (t : Tm Γ)
  → Raw-Tm (wkTm {A = A} t) ≡ Raw.wkTm {A = Raw-Ty A} (Raw-Tm t)
wkTm-raw t = refl

wkTy-sub : ∀ {Γ} {A : Ty Γ} (B : Ty Γ) → wkTy {A = A} B ≡ B [ wk {A = A} ]T
wkTy-sub {Γ} {A} B =
  Ty-ext (trans (sym (cong Raw.wkTy (Raw.[idS]T (Raw-Ty B))))
    (Raw.wkTy-[]T-r (Raw-Ty B) (Raw.idS (Raw-Ctx Γ))))

wkTm-sub : ∀ {Γ} {A : Ty Γ} (t : Tm Γ) → t [ wk {A = A} ]t ≡ wkTm {A = A} t
wkTm-sub {Γ} {A} t =
  Tm-ext (trans (sym (Raw.wkTm-[]t-r (Raw-Tm t) (Raw.idS (Raw-Ctx Γ))))
    (trans (cong (Raw.wkTm {A = Raw-Ty A}) (Raw.[idS]t (Raw-Tm t)))
      (sym (wkTm-raw {A = A} t))))

wkTy-[]T′ : ∀ {Γ Δ} {A : Ty Δ} {σ : Sub Γ Δ} {B : Ty Γ}
  → wkTy {A = B} (A [ σ ]T) ≡ A [ wkSub {A = B} σ ]T
wkTy-[]T′ {A = A} {σ = σ} = Ty-ext (Raw.wkTy-[]T-r (Raw-Ty A) (Raw-Sub σ))

wkSub-∘-r : ∀ {Θ Δ} {A : Ty Δ} → (τ : Sub Δ Θ)
  → wkSub {A = A} τ ≡ τ ∘ wk {Γ = Δ} {A = A}
wkSub-∘-r {Δ = Δ} τ =
  Sub-ext (trans (sym (cong Raw.wkSub (Raw.∘-idS-r (Raw-Sub τ))))
    (Raw.wkSub-∘-r (Raw-Sub τ) (Raw.idS (Raw-Ctx Δ))))

vz-wkSub-hasTySub : ∀ {Γ Δ} {A : Ty Δ} → (σ : Sub Γ Δ)
  → HasTySub (vz {A = A [ σ ]T}) A (wkSub {A = A [ σ ]T} σ)
vz-wkSub-hasTySub {A = A} σ =
  Raw.computed-hasTySub
    (hasTy-conv
      {t = vz {A = A [ σ ]T}}
      {A = wkTy (A [ σ ]T)}
      {B = A [ wkSub {A = A [ σ ]T} σ ]T}
      (vz-hasTy {A = A [ σ ]T})
      (wkTy-[]T′ {A = A} {σ = σ} {B = A [ σ ]T}))

vz-snoc-sub-hasTySub : ∀ {Θ : Ctx} → (Δ' : Ctx) → (B : Ty Θ) → (τ : Sub Δ' Θ)
  → HasTySub
      (vz {A = B [ τ ]T})
      B
      (τ ∘ wk {Γ = Δ'} {A = B [ τ ]T})
vz-snoc-sub-hasTySub Δ' B τ =
  hasTySub-conv
    {t = vz {A = B [ τ ]T}}
    {A = B}
    {B = B}
    {σ = wkSub {A = B [ τ ]T} τ}
    {τ = τ ∘ wk {Γ = Δ'} {A = B [ τ ]T}}
    (vz-wkSub-hasTySub {Γ = Δ'} {A = B} τ)
    (cong (λ ρ → B [ ρ ]T) (wkSub-∘-r {A = B [ τ ]T} τ))

lookup-zero-hasTySub : ∀ {Γ Δ : Ctx} {A : Ty Γ} → (σ : Sub Δ (Γ ▸ A))
  → HasTySub
      (lookup (zero {Γ = Γ} {A = A}) σ)
      A
      (wk {A = A} ∘ σ)
lookup-zero-hasTySub {Γ = Γ} {A = A} σ =
  Raw.computed-hasTySub
    (hasTy-conv
      {t = lookup (zero {Γ = Γ} {A = A}) σ}
      {A = wkTy A [ σ ]T}
      {B = A [ wk {A = A} ∘ σ ]T}
      (hasTy-lookup (Raw.zeroTy (Raw.wkTy-rel _)) (cast-sub σ))
      (trans
        (cong (_[ σ ]T) (wkTy-sub A))
        ([]T-∘ {A = A} {τ = wk {A = A}} {σ = σ})))

wk-snoc-sub : ∀ {Γ Δ} {A : Ty Δ} {t : Tm Γ} → (σ : Sub Γ Δ)
  → {p : HasTySub t A σ} → wk {Γ = Δ} {A = A} ∘ ⟨ σ , t ⟩:[ p ] ≡ σ
wk-snoc-sub {Δ = Δ} {t = t} σ =
  Sub-ext (trans (Raw.wkSub-∘ (Raw.idS (Raw-Ctx Δ)) (Raw-Sub σ) (Raw-Tm t))
    (raw-∘-idS-l (Raw-Sub σ)))

lookup-wkSub : ∀ {Γ Δ} {A : Ty Γ} (x : Var Δ) (σ : Sub Γ Δ)
  → lookup x (wkSub {A = A} σ) ≡ (lookup x σ) [ wk ]t
lookup-wkSub {Γ} {A = A} x σ =
  Tm-ext {Γ = Γ ▸ A} (trans (Raw.lookup-wkSub x (Raw-Sub σ))
    (trans (sym (cong (Raw.wkTm {A = Raw-Ty A}) (Raw.[idS]t (Raw.lookup x (Raw-Sub σ)))))
      (Raw.wkTm-[]t-r (Raw.lookup x (Raw-Sub σ)) (Raw.idS (Raw-Ctx Γ)))))

wkTm2 : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▸ A)} → Tm Γ → Tm ((Γ ▸ A) ▸ B)
wkTm2 {A = A} {B = B} t = wkTm {A = B} (wkTm {A = A} t)

wkTy2 : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▸ A)} → Ty Γ → Ty ((Γ ▸ A) ▸ B)
wkTy2 {A = A} {B = B} C = wkTy {A = B} (wkTy {A = A} C)

wkTy²-[]T : ∀ {Γ Δ} {A : Ty Δ} {σ : Sub Γ Δ} {B : Ty Γ} {C : Ty (Γ ▸ B)}
  → wkTy {A = C} (wkTy {A = B} (A [ σ ]T)) ≡ A [ wkSub {A = C} (wkSub {A = B} σ) ]T
wkTy²-[]T {A = A} {σ = σ} {B = B} {C = C} =
  trans (cong (wkTy {A = C}) (wkTy-[]T′ {A = A} {σ = σ} {B = B}))
        (wkTy-[]T′ {A = A} {σ = wkSub {A = B} σ} {B = C})

HasTySub-raw : ∀ {Γ Δ} {t : Tm Γ} {A : Ty Δ}
  → {σraw : RawSub (Raw-Ctx Γ) (Raw-Ctx Δ)} → (σwf : Sub-iswf σraw)
  → Raw.HasTy (Raw-Tm t) (Raw-Ty A Raw.[ σraw ]T)
  → HasTySub t A (mkSub {Γ = Γ} {Δ = Δ} σraw σwf)
HasTySub-raw σwf p = Raw.computed-hasTySub p

wkTy-snoc-sub : ∀ {Γ Δ} {A : Ty Δ} (B : Ty Δ) (σ : Sub Γ Δ) (t : Tm Γ)
  {p : HasTySub t A σ}
  → wkTy {A = A} B [ ⟨ σ , t ⟩:[ p ] ]T ≡ B [ σ ]T
wkTy-snoc-sub {A = A} B σ t =
  Ty-ext (Raw.wkTy-[]T (Raw-Ty B) (Raw-Sub σ) (Raw-Tm t))

vz-snoc-sub-ty : ∀ {Θ : Ctx} → (Δ' : Ctx) → (B : Ty Θ) → (τ : Sub Δ' Θ)
  → tyOf (var (Raw.zero {Γ = Raw-Ctx Δ'} {A = Raw-Ty (B [ τ ]T)}))
      ≡ B [ τ ∘ wk {Γ = Δ'} {A = B [ τ ]T} ]T
vz-snoc-sub-ty Δ' B τ =
  trans (wkTy-[]T′ {A = B} {σ = τ} {B = B [ τ ]T})
    (cong (λ ρ → B [ ρ ]T) (wkSub-∘-r {A = B [ τ ]T} τ))
```

## Substitution Agreement

If two substitutions agree on every variable that a type or term depends on,
their substitutions produce equal results. The relational dependency predicates
come from `1b-Dependency`; the computed equalities are produced via `Raw._[_]T`.

```agda
mutual
  sub-agree-ty-raw : ∀ {Γ Δ} (A : Ty Γ) (σ τ : Sub Δ Γ)
    → ((x : Var Γ) → D.DepVarTy x (Raw-Ty A)
    → Raw-Tm (var x [ σ ]t) ≡ Raw-Tm (var x [ τ ]t))
    → Raw-Ty A Raw.[ Raw-Sub σ ]T ≡ Raw-Ty A Raw.[ Raw-Sub τ ]T
  sub-agree-ty-raw (mkTy Raw.⋆ ⋆wf) σ τ agree = refl
  sub-agree-ty-raw
    (mkTy (Raw.[ A ] t ⇒ u)
      (hom-wf (mkTyR .A Awf) {mkTmR .t twf} {mkTmR .u uwf} p q))
    σ τ agree =
    trans
      (cong
        (λ B' → Raw.[ B' ] (t Raw.[ Raw-Sub σ ]t) ⇒ (u Raw.[ Raw-Sub σ ]t))
        (sub-agree-ty-raw
          (mkTy A Awf) σ τ
          (λ x dx → agree x (D.dep-base dx))))
      (cong₂
        (λ t' u' → Raw.[ A Raw.[ Raw-Sub τ ]T ] t' ⇒ u')
        (sub-agree-tm-raw
          (mkTm t twf) σ τ
          (λ x dx → agree x (D.dep-src dx)))
        (sub-agree-tm-raw
          (mkTm u uwf) σ τ
          (λ x dx → agree x (D.dep-tgt dx))))

  sub-agree-tm-raw : ∀ {Γ Δ} (t : Tm Γ) (σ τ : Sub Δ Γ) → ((x : Var Γ)
    → D.DepVarTm x (Raw-Tm t) → Raw-Tm (var x [ σ ]t) ≡ Raw-Tm (var x [ τ ]t))
    → Raw-Tm t Raw.[ Raw-Sub σ ]t ≡ Raw-Tm t Raw.[ Raw-Sub τ ]t
  sub-agree-tm-raw (mkTm (Raw.var y) (var-wf .y)) σ τ agree =
    agree y (D.dep-var (D.dep-var-var-refl y))
  sub-agree-tm-raw {Γ = Γ} {Δ = Δ}
    (mkTm (Raw.coh A u v γ)
      (coh-wf {Δ = Θ} ps Δwf tA tu tv p q r (mkSubR .γ γwf)))
    σ τ agree =
    cong (Raw.coh A u v)
      (sub-agree-sub-raw
        {Γ = mkCtx Θ Δwf} {Δ = Δ} {Θ = Γ}
        (mkSub γ γwf) σ τ
        (λ x dx → agree x (D.dep-coh dx)))

  sub-agree-sub-raw : ∀ {Γ Δ Θ} (υ : Sub Θ Γ) (σ τ : Sub Δ Θ)
    → ((x : Var Θ)
      → D.DepVarSub x (Raw-Sub υ)
      → Raw-Tm (var x [ σ ]t) ≡ Raw-Tm (var x [ τ ]t))
    → Raw-Sub υ Raw.∘ Raw-Sub σ ≡ Raw-Sub υ Raw.∘ Raw-Sub τ
  sub-agree-sub-raw (mkSub Raw.◆S ◆Swf) σ τ agree = refl
  sub-agree-sub-raw {Δ = Δ} {Θ = Θ}
    (mkSub (Raw.⟨ υ , t ⟩)
      (⟨_,_⟩:[_]wf {A = A0} (mkSubR .υ υwf) (mkTmR .t twf) p))
    σ τ agree =
    cong₂ Raw.⟨_,_⟩
      (sub-agree-sub-raw
        {Γ = mkCtx _ (sub-cod-iswf υ υwf)} {Δ = Δ} {Θ = Θ}
        (mkSub υ υwf) σ τ
        (λ x dx → agree x (D.dep-sub-there dx)))
      (sub-agree-tm-raw
        (mkTm t twf) σ τ
        (λ x dx → agree x (D.dep-sub-here dx)))

sub-agree-ty : ∀ {Γ Δ} (A : Ty Γ) (σ τ : Sub Δ Γ)
  → ((x : Var Γ)
    → D.DepVarTy x (Raw-Ty A)
    → var x [ σ ]t ≡ var x [ τ ]t)
  → A [ σ ]T ≡ A [ τ ]T
sub-agree-ty A σ τ agree =
  Ty-ext (sub-agree-ty-raw A σ τ (λ x dx → cong Raw-Tm (agree x dx)))

sub-agree-tm : ∀ {Γ Δ} (t : Tm Γ) (σ τ : Sub Δ Γ)
  → ((x : Var Γ)
    → D.DepVarTm x (Raw-Tm t)
    → var x [ σ ]t ≡ var x [ τ ]t)
  → t [ σ ]t ≡ t [ τ ]t
sub-agree-tm t σ τ agree =
  Tm-ext (sub-agree-tm-raw t σ τ (λ x dx → cong Raw-Tm (agree x dx)))
```

## Computed Extension Cells

`hom-type-ext` and `ext-ctx` build the new cell type / extended context over a
dangling variable. Their types mention the computed `wkTy`, while the dangling
evidence itself remains relational. The `coh-*-typed` lemmas give the
(substituted) hom-type of a specialized coherence, and `coh-sub` records
substitution into a coherence.

```agda
private
  hom-type-ext-src-hasTy : ∀ {Γ : Ctx} {k : ℕ} {Γps : IsPsCtx Γ k}
    {x : Var Γ} {A : Ty Γ} {n : ℕ} →
    IsDangling Γps x A n → HasTy (vs {A = A} x) (wkTy {A = A} A)
  hom-type-ext-src-hasTy {A = A} d =
    Raw.varTy (Raw.succTy (P.isDangling-hasTyVar d) (Raw.wkTy-rel (Raw-Ty A)))

  hom-type-ext-tgt-hasTy : ∀ {Γ : Ctx} {k : ℕ} {Γps : IsPsCtx Γ k}
    {x : Var Γ} {A : Ty Γ} {n : ℕ} →
    IsDangling Γps x A n → HasTy (vz {A = A}) (wkTy {A = A} A)
  hom-type-ext-tgt-hasTy {A = A} d =
    Raw.varTy (Raw.zeroTy (Raw.wkTy-rel (Raw-Ty A)))

-- The hom-type of the extension cell, built from the new positive typing
-- witnesses rather than from var-to-type.
hom-type-ext : ∀ {Γ : Ctx} {k : ℕ} {Γps : IsPsCtx Γ k}
  {x : Var Γ} {A : Ty Γ} {n : ℕ} →
  IsDangling Γps x A n → Ty (Γ ▸ A)
hom-type-ext {Γps = Γps} {x = x} {A = A} d =
  [ wkTy {A = A} A ] vs {A = A} x ⇒ vz {A = A}
    :[ hom-type-ext-src-hasTy {Γps = Γps} {x = x} {A = A} d
     , hom-type-ext-tgt-hasTy {Γps = Γps} {x = x} {A = A} d ]

-- The context obtained by extending along a dangling variable.
ext-ctx : ∀ {Γ : Ctx} {k : ℕ} {Γps : IsPsCtx Γ k}
  {x : Var Γ} {A : Ty Γ} {n : ℕ} →
  IsDangling Γps x A n → Ctx
ext-ctx {Γ = Γ} {A = A} d = (Γ ▸ A) ▸ hom-type-ext d

-- A coherence specialized along the identity substitution has the expected
-- hom-type over its chosen endpoints. 2b reuses this both for composition
-- and for the universal whiskering coherences.
coh-id-typed : ∀ {Δ : Ctx} {k : ℕ} → (ps : IsPsCtx Δ k) → (A : Ty Δ) → (u v : Tm Δ)
  → (pu : HasTy u A) → (pv : HasTy v A)
  → (full : Full ps (Raw-Ty A) (Raw-Tm u) (Raw-Tm v))
  → HasTy
      (coh ps A u v pu pv full (idS Δ))
      ([ A ] u ⇒ v :[ pu , pv ])
coh-id-typed {Δ = Δ} ps A u v pu pv full =
  subst
    (Raw.HasTy (Raw-Tm (coh ps A u v pu pv full (idS Δ))))
    (Raw.[idS]T (Raw.[ Raw-Ty A ] Raw-Tm u ⇒ Raw-Tm v))
    (Raw.cohTy (Raw.substTy (Raw.[ Raw-Ty A ] Raw-Tm u ⇒ Raw-Tm v) (Raw.idS (Raw-Ctx Δ))))

-- A coherence specialized along any substitution has the substituted hom-type.
coh-typed : ∀ {Γ Δ : Ctx} {k : ℕ} → (ps : IsPsCtx Δ k) → (A : Ty Δ) → (u v : Tm Δ)
  → (pu : HasTy u A) → (pv : HasTy v A)
  → (full : Full ps (Raw-Ty A) (Raw-Tm u) (Raw-Tm v))
  → (σ : Sub Γ Δ)
  → HasTy
      (coh ps A u v pu pv full σ)
      (([ A ] u ⇒ v :[ pu , pv ]) [ σ ]T)
coh-typed ps A u v pu pv full σ =
  Raw.cohTy (Raw.substTy (Raw.[ Raw-Ty A ] Raw-Tm u ⇒ Raw-Tm v) (Raw-Sub σ))

-- Substituting a coherence just composes its underlying substitution slot.
coh-sub : ∀ {Γ Δ Θ : Ctx} {k : ℕ} → (ps : IsPsCtx Θ k) → (A : Ty Θ)
  → (u v : Tm Θ) → (pu : HasTy u A) → (pv : HasTy v A)
  → (full : Full ps (Raw-Ty A) (Raw-Tm u) (Raw-Tm v))
  → (τ : Sub Δ Θ) → (σ : Sub Γ Δ)
  → (coh ps A u v pu pv full τ) [ σ ]t ≡ coh ps A u v pu pv full (τ ∘ σ)
coh-sub ps A u v pu pv full τ σ = Tm-ext refl
```

## Helpers for Naturality

These lemmas support the naturality construction in `3b-Naturality`. Triple
weakening of types and lookups (`wkTy³-[]T`, `lookup-wkSub³`) arise because the
naturality context adds three variables for each selected variable.
`homTy-[]T` expresses that substituting into a hom-type commutes with the
hom-type constructor.

```agda
wkTy³-[]T : ∀ {Γ Δ} {A : Ty Δ} {σ : Sub Γ Δ}
  {B : Ty Γ} {C : Ty (Γ ▸ B)} {D : Ty ((Γ ▸ B) ▸ C)}
  → wkTy {A = D} (wkTy {A = C} (wkTy {A = B} (A [ σ ]T)))
    ≡ A [ wkSub {A = D} (wkSub {A = C} (wkSub {A = B} σ)) ]T
wkTy³-[]T {A = A} {σ = σ} {B = B} {C = C} {D = D} =
  trans (cong (wkTy {A = D}) (wkTy²-[]T {A = A} {σ = σ} {B = B} {C = C}))
        (wkTy-[]T′ {A = A} {σ = wkSub {A = C} (wkSub {A = B} σ)} {B = D})

lookup-wkSub³ : ∀ {Γ Δ} {A : Ty Γ} {B : Ty (Γ ▸ A)}
  {C : Ty ((Γ ▸ A) ▸ B)} (x : Var Δ) (σ : Sub Γ Δ)
  → lookup x (wkSub {A = C} (wkSub {A = B} (wkSub {A = A} σ)))
    ≡ ((lookup x σ) [ wk ]t) [ wk ]t [ wk ]t
lookup-wkSub³ {A = A} {B = B} {C = C} x σ =
  trans (lookup-wkSub {A = C} x (wkSub {A = B} (wkSub {A = A} σ)))
    (cong (_[ wk {A = C} ]t)
      (trans (lookup-wkSub {A = B} x (wkSub {A = A} σ))
        (cong (_[ wk {A = B} ]t) (lookup-wkSub {A = A} x σ))))

homTy-[]T : ∀ {Γ Δ} {A : Ty Δ} {x y : Tm Δ} {σ : Sub Γ Δ}
  → (px : HasTy x A) → (py : HasTy y A)
  → ([ A ] x ⇒ y :[ px , py ]) [ σ ]T
    ≡ [ A [ σ ]T ] (x [ σ ]t) ⇒ (y [ σ ]t)
      :[ tmSub-typed {Γ = Γ} {Δ = Δ} {t = x} {A = A} {σ = σ} px
       , tmSub-typed {Γ = Γ} {Δ = Δ} {t = y} {A = A} {σ = σ} py ]
homTy-[]T px py = Ty-ext refl
```
