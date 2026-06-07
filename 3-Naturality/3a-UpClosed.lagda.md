# 3a-UpClosed: Typed Selector Dependency

This module contains the typed selector infrastructure used by coherence
triples and later naturality constructions: up-closed selectors, typed
selected-dependency transport, and inverse image of selectors along
substitutions.

**Up-closed selectors** `Up Γ` are selectors `SelVar (Raw-Ctx Γ)` together with
an up-closure proof: if a variable is unset, its type must be type-independent of
the selected variables.

**Dependency transport** (`dep-tm-sub-transitivityR` and friends) shows that if
`x` depends on `σ(y)` and `y` depends on a type/term/sub, then `x` depends on
the result of composing the sub with `σ`. These chain the proof-relevant
dependency predicates from `1b-Dependency` through substitutions.

**Selected-by view** (`sel-dep-tm-view`) decides, for a given selector and term,
whether any selected variable has a dependency path into that term. The search
uses decidable dependency (`dep-var-tm?`) inside the `SelectedView` data type.

**Inverse image** (`inv-img`) computes, from a substitution `σ : Sub Δ Γ` and
an up-closed selector `X : Up Δ`, the up-closed selector on `Γ` consisting of
those variables `y` such that `σ(y)` depends on some variable in `X`.

This module is the **relational core**. It imports only the relational
`1-preCaTT`/`2-CaTT` cores and contains the proposition-facing selector
infrastructure: up-closed selectors, the relation-native selected-dependency
transport family (parameterized by explicit `SubstTy`/`SubstTm`/`CompSub`/`WkTm`
witnesses rather than by computed substitution or weakening outputs), and the
inverse image of selectors along substitutions characterized through
`SelDepSubAt`. The canonical functions `inv-img-sel` and `inv-img` stay here
because they feed downstream type indices. Compatibility wrappers that genuinely
need computed substitution or weakening live in `3a-UpClosed-Comp`; computed
lookup reformulations are intentionally not part of the live API.

```agda
module 3a-UpClosed where

import 1a-RawSyntax as Raw
import 1b-Dependency as D
open import 2a-CaTT as C

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (Dec; yes; no)

open Raw using (RawCtx; RawTy; RawTm; RawSub; RawVar)
```

## Up-Closed Selectors

`is-upclosed X` is an inductive proof that the selector `X` is up-closed: the
base is always up-closed; `snoc-set` allows adding a set variable freely;
`snoc-unset` allows adding an unset variable only if the type of the new
variable is independent of all selected variables (`SelTypeIndep`). The record
`Up Γ` bundles a selector with its up-closure proof. `DropLast` removes the
outermost (most recent) variable from an up-closed selector on `Γ ▸ A`.

```agda
data is-upclosed : {Γ : RawCtx} → D.SelVar Γ → Set₁ where
  base :
    is-upclosed D.sel-base
  snoc-set :
    ∀ {Γ : RawCtx} {A : RawTy Γ} (X : D.SelVar Γ)
    → is-upclosed X
    → is-upclosed (D.sel-set A X)
  snoc-unset :
    ∀ {Γ : RawCtx} {A : RawTy Γ} (X : D.SelVar Γ)
    → is-upclosed X
    → D.SelTypeIndep X A
    → is-upclosed (D.sel-unset A X)

record Up (Γ : Ctx) : Set₁ where
  pattern
  constructor mk
  field
    sel     : D.SelVar (Raw-Ctx Γ)
    is-upcl : is-upclosed sel

DropLast : {Γ : Ctx} {A : Ty Γ} → Up (Γ ▸ A) → Up Γ
DropLast (mk (D.sel-set _ X)   (snoc-set .X X-up))     = mk X X-up
DropLast (mk (D.sel-unset _ X) (snoc-unset .X X-up _)) = mk X X-up
```

## Typed Selector and Transport Helpers

`tm-dep X t` is the typed alias for `SelDepTm (Up.sel X) (Raw-Tm t)`.
The main results in this section are the relation-native dependency transport
lemmas (`dep-sub-at-var-transR`, `dep-ty-substR`, `dep-tm-substR`,
`dep-sub-compR`): given that variable `x` depends on `σ(y)` and `y` depends on
something, these chain the dependency through the substitution `σ`. They take
the substitution as a *well-formed* `SubR` (so the variable case can read the
head term's typing witness `typed-sub subA ht` out of the snoc), together with
explicit relational `SubstTy`/`SubstTm`/`CompSub` evidence and explicit result
syntax — no computed `_[_]T`/`_[_]t`/`_∘_`/`lookup`. The variable case reuses the
relational typing bridge `D.dep-hasTy→dep-tm` and the structural lookup-inverse
`D.dep-sub-at→dep-substVar`. The public lemma `sel-dep-ty-sub-transitivity`
packages these for use with `SelectedBy`; selecting a typed term from a typed
dependency is handled directly by `D.sel-dep-hasTy→tm`.

```agda
tm-dep : {Γ : Ctx} → Up Γ → Tm Γ → Set₁
tm-dep X t = D.SelDepTm (Up.sel X) (Raw-Tm t)

{-# TERMINATING #-}
mutual
  -- Variable-to-variable dependency transferred through σ. The `dep-ty` case
  -- reads the head term's typing witness `typed-sub subA ht` out of the
  -- well-formed snoc substitution.
  dep-sub-at-var-transR :
    ∀ {Γ Δ : RawCtx}
    → (x : RawVar Γ) → (σ : SubR Γ Δ) → (y z : RawVar Δ)
    → D.DepVarSubAt x (Raw-SubR σ) y
    → D.DepVarVar y z
    → D.DepVarSubAt x (Raw-SubR σ) z
  dep-sub-at-var-transR x
      (mkSubR (Raw.⟨ _ , _ ⟩) (⟨_,_⟩:[_]wf _ _ _))
      Raw.zero Raw.zero
      (D.dep-sub-at-here dt) D.dep-refl =
    D.dep-sub-at-here dt
  dep-sub-at-var-transR x
      (mkSubR (Raw.⟨ σraw , traw ⟩)
        (⟨_,_⟩:[_]wf {A = A} (mkSubR .σraw σwf) (mkTmR .traw twf)
          (Raw.typed-sub subA ht)))
      (Raw.succ y') Raw.zero
      (D.dep-sub-at-there dσy') (D.dep-ty dy) =
    D.dep-sub-at-here
      (D.dep-hasTy→dep-tm x ht
        (dep-ty-substR x (mkSubR σraw σwf) y' dσy' subA dy))
  dep-sub-at-var-transR x
      (mkSubR (Raw.⟨ _ , _ ⟩) (⟨_,_⟩:[_]wf _ _ _))
      Raw.zero (Raw.succ _) _ ()
  dep-sub-at-var-transR x
      (mkSubR (Raw.⟨ σraw , _ ⟩)
        (⟨_,_⟩:[_]wf {A = A} (mkSubR .σraw σwf) _ _))
      (Raw.succ y') (Raw.succ z')
      (D.dep-sub-at-there dσy') (D.dep-weak dyz') =
    D.dep-sub-at-there
      (dep-sub-at-var-transR x (mkSubR σraw σwf) y' z' dσy' dyz')

  -- A dependency `y` in `A`, together with `SubstTy A σ B`, transfers to a
  -- dependency `x` in the explicit substituted type `B`.
  dep-ty-substR :
    ∀ {Γ Δ : RawCtx} {A : RawTy Δ} {B : RawTy Γ}
    → (x : RawVar Γ) → (σ : SubR Γ Δ) → (y : RawVar Δ)
    → D.DepVarSubAt x (Raw-SubR σ) y
    → Raw.SubstTy A (Raw-SubR σ) B
    → D.DepVarTy y A
    → D.DepVarTy x B
  dep-ty-substR x σ y dσ Raw.sub-⋆ ()
  dep-ty-substR x σ y dσ (Raw.sub-hom pA pt pu) (D.dep-base d) =
    D.dep-base (dep-ty-substR x σ y dσ pA d)
  dep-ty-substR x σ y dσ (Raw.sub-hom pA pt pu) (D.dep-src d) =
    D.dep-src (dep-tm-substR x σ y dσ pt d)
  dep-ty-substR x σ y dσ (Raw.sub-hom pA pt pu) (D.dep-tgt d) =
    D.dep-tgt (dep-tm-substR x σ y dσ pu d)

  -- The term-level companion, taking `SubstTm t σ u`.
  dep-tm-substR :
    ∀ {Γ Δ : RawCtx} {t : RawTm Δ} {u : RawTm Γ}
    → (x : RawVar Γ) → (σ : SubR Γ Δ) → (y : RawVar Δ)
    → D.DepVarSubAt x (Raw-SubR σ) y
    → Raw.SubstTm t (Raw-SubR σ) u
    → D.DepVarTm y t
    → D.DepVarTm x u
  dep-tm-substR x σ y dσ (Raw.sub-var p) (D.dep-var dyz) =
    D.dep-sub-at→dep-substVar p
      (dep-sub-at-var-transR x σ y _ dσ dyz)
  dep-tm-substR x σ y dσ (Raw.sub-coh p) (D.dep-coh d) =
    D.dep-coh (dep-sub-compR x σ y dσ p d)

  -- The substitution-composition companion, taking `CompSub τ σ υ`.
  dep-sub-compR :
    ∀ {Γ Δ Θ : RawCtx} {τ : RawSub Δ Θ} {υ : RawSub Γ Θ}
    → (x : RawVar Γ) → (σ : SubR Γ Δ) → (y : RawVar Δ)
    → D.DepVarSubAt x (Raw-SubR σ) y
    → Raw.CompSub τ (Raw-SubR σ) υ
    → D.DepVarSub y τ
    → D.DepVarSub x υ
  dep-sub-compR x σ y dσ Raw.comp-empty ()
  dep-sub-compR x σ y dσ (Raw.comp-snoc p pt) (D.dep-sub-here dt) =
    D.dep-sub-here (dep-tm-substR x σ y dσ pt dt)
  dep-sub-compR x σ y dσ (Raw.comp-snoc p pt) (D.dep-sub-there dτ') =
    D.dep-sub-there (dep-sub-compR x σ y dσ p dτ')

sel-dep-ty-sub-transitivity :
  ∀ {Γ Δ : Ctx}
  → {s : D.SelVar (Raw-Ctx Γ)} {σ : Sub Γ Δ} {y : Var Δ}
  → {A : Ty Δ} {B : RawTy (Raw-Ctx Γ)}
  → D.SelDepSubAt s (Raw-Sub σ) y
  → Raw.SubstTy (Raw-Ty A) (Raw-Sub σ) B
  → D.DepVarTy y (Raw-Ty A)
  → D.SelDepTy s B
sel-dep-ty-sub-transitivity {σ = σ} dσ subA dA =
  D.selected-by
    (D.SelectedBy.selected-var dσ)
    (D.SelectedBy.selected-here dσ)
    (dep-ty-substR
      (D.SelectedBy.selected-var dσ)
      (cast-sub σ)
      _
      (D.SelectedBy.selected-proof dσ)
      subA
      dA)
```

## Internal Search Machinery

`SelectedView s P` is a two-constructor type: `selected d` when there exists a
variable in `s` satisfying `P`, and `outside ind` when no variable in `s`
satisfies `P`. The private mutual block `dep-var-var?`, `dep-var-ty?`,
`dep-var-tm?`, `dep-var-sub-at?`, `dep-var-sub?` implement decidability of the
proof-relevant dependency predicates by recursing on the raw syntax.
`selected-by-view` folds these decisions over a selector to produce a
`SelectedView`. The public `sel-dep-tm-view` applies this to term dependency.

```agda
data SelectedView {Γ : RawCtx}
  (s : D.SelVar Γ) (P : RawVar Γ → Set₁) : Set₁ where
  selected : D.SelectedBy s P → SelectedView s P
  outside  : D.SelNone s P → SelectedView s P

private
  mutual
    dep-var-var? : {Γ : RawCtx} (x y : RawVar Γ) → Dec (D.DepVarVar x y)
    dep-var-var? {Γ = _ Raw.▸ _} Raw.zero Raw.zero = yes D.dep-refl
    dep-var-var? {Γ = _ Raw.▸ _} Raw.zero (Raw.succ y) = no λ ()
    dep-var-var? {Γ = Γ Raw.▸ A} (Raw.succ x) Raw.zero with dep-var-ty? x A
    ... | yes d = yes (D.dep-ty d)
    ... | no nd = no λ { (D.dep-ty d) → nd d }
    dep-var-var? {Γ = _ Raw.▸ _} (Raw.succ x) (Raw.succ y) with dep-var-var? x y
    ... | yes d = yes (D.dep-weak d)
    ... | no nd = no λ { (D.dep-weak d) → nd d }

    dep-var-ty? : {Γ : RawCtx} (x : RawVar Γ) (A : RawTy Γ) → Dec (D.DepVarTy x A)
    dep-var-ty? x Raw.⋆ = no λ ()
    dep-var-ty? x (Raw.[ A ] t ⇒ u) with dep-var-ty? x A | dep-var-tm? x t | dep-var-tm? x u
    ... | yes d | _ | _ = yes (D.dep-base d)
    ... | no _ | yes d | _ = yes (D.dep-src d)
    ... | no _ | no _ | yes d = yes (D.dep-tgt d)
    ... | no ndA | no ndt | no ndu =
      no λ
        { (D.dep-base d) → ndA d
        ; (D.dep-src d)  → ndt d
        ; (D.dep-tgt d)  → ndu d
        }

    dep-var-tm? : {Γ : RawCtx} (x : RawVar Γ) (t : RawTm Γ) → Dec (D.DepVarTm x t)
    dep-var-tm? x (Raw.var y) with dep-var-var? x y
    ... | yes d = yes (D.dep-var d)
    ... | no nd = no λ { (D.dep-var d) → nd d }
    dep-var-tm? x (Raw.coh A u v σ) with dep-var-sub? x σ
    ... | yes d = yes (D.dep-coh d)
    ... | no nd = no λ { (D.dep-coh d) → nd d }

    dep-var-sub-at? :
      {Γ Δ : RawCtx} (x : RawVar Γ) (σ : RawSub Γ Δ) (y : RawVar Δ)
      → Dec (D.DepVarSubAt x σ y)
    dep-var-sub-at? x (Raw.⟨ σ , t ⟩) Raw.zero with dep-var-tm? x t
    ... | yes d = yes (D.dep-sub-at-here d)
    ... | no nd = no λ { (D.dep-sub-at-here d) → nd d }
    dep-var-sub-at? x (Raw.⟨ σ , t ⟩) (Raw.succ y) with dep-var-sub-at? x σ y
    ... | yes d = yes (D.dep-sub-at-there d)
    ... | no nd = no λ { (D.dep-sub-at-there d) → nd d }

    dep-var-sub? : {Γ Δ : RawCtx} (x : RawVar Γ) (σ : RawSub Γ Δ) → Dec (D.DepVarSub x σ)
    dep-var-sub? x Raw.◆S = no λ ()
    dep-var-sub? x (Raw.⟨ σ , t ⟩) with dep-var-tm? x t | dep-var-sub? x σ
    ... | yes d | _ = yes (D.dep-sub-here d)
    ... | no _ | yes d = yes (D.dep-sub-there d)
    ... | no ndt | no ndσ =
      no λ
        { (D.dep-sub-here d)  → ndt d
        ; (D.dep-sub-there d) → ndσ d
        }

  selected-by-view :
    {Γ : RawCtx}
    → (s : D.SelVar Γ) → (P : RawVar Γ → Set₁)
    → ((x : RawVar Γ) → Dec (P x))
    → SelectedView s P
  selected-by-view D.sel-base P P? = outside λ ()
  selected-by-view (D.sel-set A s) P P? with P? Raw.zero
  ... | yes p = selected (D.selected-by Raw.zero D.here p)
  ... | no np with selected-by-view s (λ x → P (Raw.succ x)) (λ x → P? (Raw.succ x))
  ...   | selected d =
          selected
            (D.selected-by
              (Raw.succ (D.SelectedBy.selected-var d))
              (D.there-set (D.SelectedBy.selected-here d))
              (D.SelectedBy.selected-proof d))
  ...   | outside ind =
          outside λ
            { D.here p → np p
            ; (D.there-set px) p → ind px p
            }
  selected-by-view (D.sel-unset A s) P P? with selected-by-view s (λ x → P (Raw.succ x)) (λ x → P? (Raw.succ x))
  ... | selected d =
        selected
          (D.selected-by
            (Raw.succ (D.SelectedBy.selected-var d))
            (D.there-unset (D.SelectedBy.selected-here d))
            (D.SelectedBy.selected-proof d))
  ... | outside ind =
        outside λ
          { (D.there-unset px) p → ind px p }

  sel-dep-tm-view-priv :
    {Γ : Ctx} → (X : Up Γ) → (t : Tm Γ) →
    SelectedView (Up.sel X) (λ x → D.DepVarTm x (Raw-Tm t))
  sel-dep-tm-view-priv X t =
    selected-by-view (Up.sel X) (λ x → D.DepVarTm x (Raw-Tm t))
      (λ x → dep-var-tm? x (Raw-Tm t))

sel-dep-tm-view :
  {Γ : Ctx} → (X : Up Γ) → (t : Tm Γ) →
  SelectedView (Up.sel X) (λ x → D.DepVarTm x (Raw-Tm t))
sel-dep-tm-view = sel-dep-tm-view-priv

private
  up-closure-sel : {Γ : RawCtx} → D.SelVar Γ → D.SelVar Γ
  up-closure-sel D.sel-base = D.sel-base
  up-closure-sel (D.sel-set A X) =
    D.sel-set A (up-closure-sel X)
  up-closure-sel (D.sel-unset A X)
      with selected-by-view
             (up-closure-sel X)
             (λ x → D.DepVarTy x A)
             (λ x → dep-var-ty? x A)
  ... | selected _ =
    D.sel-set A (up-closure-sel X)
  ... | outside _ =
    D.sel-unset A (up-closure-sel X)

  up-closure-is-upclosed :
    {Γ : RawCtx} → (X : D.SelVar Γ) → is-upclosed (up-closure-sel X)
  up-closure-is-upclosed D.sel-base = base
  up-closure-is-upclosed (D.sel-set A X) =
    snoc-set (up-closure-sel X) (up-closure-is-upclosed X)
  up-closure-is-upclosed (D.sel-unset A X)
      with selected-by-view
             (up-closure-sel X)
             (λ x → D.DepVarTy x A)
             (λ x → dep-var-ty? x A)
  ... | selected _ =
    snoc-set (up-closure-sel X) (up-closure-is-upclosed X)
  ... | outside indep =
    snoc-unset (up-closure-sel X) (up-closure-is-upclosed X) indep

  empty-sel : {Γ : RawCtx} → D.SelVar Γ
  empty-sel {Γ = Raw.◆} = D.sel-base
  empty-sel {Γ = Γ Raw.▸ A} = D.sel-unset A (empty-sel {Γ = Γ})

  singleton-sel-raw : {Γ : RawCtx} → RawVar Γ → D.SelVar Γ
  singleton-sel-raw {Γ = Raw.◆} ()
  singleton-sel-raw {Γ = Γ Raw.▸ A} Raw.zero =
    D.sel-set A (empty-sel {Γ = Γ})
  singleton-sel-raw {Γ = Γ Raw.▸ A} (Raw.succ x) =
    D.sel-unset A (singleton-sel-raw x)

  empty-upclose-no-select :
    {Γ : RawCtx} {x : RawVar Γ} →
    D.selects (up-closure-sel (empty-sel {Γ = Γ})) x → ⊥
  empty-upclose-no-select {Γ = Raw.◆} {()} px
  empty-upclose-no-select {Γ = Γ Raw.▸ A} {Raw.zero} px
    with selected-by-view
      (up-closure-sel (empty-sel {Γ = Γ}))
      (λ x → D.DepVarTy x A)
      (λ x → dep-var-ty? x A)
      | px
  ... | selected d | D.here =
    empty-upclose-no-select
      {Γ = Γ}
      {x = D.SelectedBy.selected-var d}
      (D.SelectedBy.selected-here d)
  ... | outside _ | ()
  empty-upclose-no-select {Γ = Γ Raw.▸ A} {Raw.succ x} px
    with selected-by-view
      (up-closure-sel (empty-sel {Γ = Γ}))
      (λ x → D.DepVarTy x A)
      (λ x → dep-var-ty? x A)
      | px
  ... | selected d | D.there-set px′ =
    empty-upclose-no-select {Γ = Γ} {x = x} px′
  ... | outside _ | D.there-unset px′ =
    empty-upclose-no-select {Γ = Γ} {x = x} px′

up-closure : {Γ : Ctx} → D.SelVar (Raw-Ctx Γ) → Up Γ
up-closure X = mk (up-closure-sel X) (up-closure-is-upclosed X)

singleton-sel : {Γ : Ctx} → (x : Var Γ) → D.SelVar (Raw-Ctx Γ)
singleton-sel x = singleton-sel-raw x

var-upclose : {Γ : Ctx} → (x : Var Γ) → Up Γ
var-upclose {Γ} x = up-closure (singleton-sel {Γ} x)

var-upclose-self-selects :
  {Γ : Ctx} →
  (x : Var Γ) →
  D.selects (Up.sel (var-upclose {Γ = Γ} x)) x
var-upclose-self-selects {Γ = Γ} x with ctx-view Γ | x
... | ◆-view | ()
... | ▸-view {Γ = Γ′} A | Raw.zero =
  D.here
... | ▸-view {Γ = Γ′} A | Raw.succ x′
    with selected-by-view
      (up-closure-sel (singleton-sel {Γ = Γ′} x′))
      (λ y → D.DepVarTy y (Raw-Ty A))
      (λ y → dep-var-ty? y (Raw-Ty A))
...   | selected _ =
  D.there-set (var-upclose-self-selects {Γ = Γ′} x′)
...   | outside _ =
  D.there-unset (var-upclose-self-selects {Γ = Γ′} x′)

var-upclose-succ-here :
  {Γ : Ctx} {A : Ty Γ} {x : Var Γ} →
  D.SelDepTy (Up.sel (var-upclose {Γ = Γ} x)) (Raw-Ty A) →
  D.selects
    (Up.sel (var-upclose {Γ = Γ ▸ A} (succ {Γ = Γ} {A = A} x)))
    Raw.zero
var-upclose-succ-here {Γ = Γ} {A = A} {x = x} dep
    with selected-by-view
      (up-closure-sel (singleton-sel {Γ = Γ} x))
      (λ y → D.DepVarTy y (Raw-Ty A))
      (λ y → dep-var-ty? y (Raw-Ty A))
... | selected _ =
  D.here
... | outside no-dep =
  ⊥-elim
    (no-dep
      (D.SelectedBy.selected-here dep)
      (D.SelectedBy.selected-proof dep))

var-upclose-succ-there :
  {Γ : Ctx} {A : Ty Γ} {x z : Var Γ} →
  D.selects (Up.sel (var-upclose {Γ = Γ} x)) z →
  D.selects
    (Up.sel (var-upclose {Γ = Γ ▸ A} (succ {Γ = Γ} {A = A} x)))
    (Raw.succ z)
var-upclose-succ-there {Γ = Γ} {A = A} {x = x} p
    with selected-by-view
      (up-closure-sel (singleton-sel {Γ = Γ} x))
      (λ y → D.DepVarTy y (Raw-Ty A))
      (λ y → dep-var-ty? y (Raw-Ty A))
... | selected _ =
  D.there-set p
... | outside _ =
  D.there-unset p

var-upclose-wk-dep-rel :
  {Γ : Ctx} {A : Ty Γ} {x : Var Γ} →
  (t : Tm Γ) → {t' : RawTm (Raw-Ctx (Γ ▸ A))} →
  Raw.WkTm {A = Raw-Ty A} (Raw-Tm t) t' →
  D.SelDepTm
    (Up.sel (var-upclose {Γ = Γ ▸ A} (succ {Γ = Γ} {A = A} x))) t' →
  tm-dep (var-upclose {Γ = Γ} x) t
var-upclose-wk-dep-rel {Γ = Γ} {A = A} {x = x₀} t wp dep
    with selected-by-view
      (up-closure-sel (singleton-sel {Γ = Γ} x₀))
      (λ x → D.DepVarTy x (Raw-Ty A))
      (λ x → dep-var-ty? x (Raw-Ty A))
      | dep
... | selected _ | D.selected-by Raw.zero D.here dz =
  ⊥-elim (D.dep-wkTm-vz-absurd wp dz)
... | selected _ | D.selected-by (Raw.succ x) (D.there-set px) dz =
  D.selected-by x px (D.dep-wkTm-vs-ind x wp dz)
... | outside _ | D.selected-by (Raw.succ x) (D.there-unset px) dz =
  D.selected-by x px (D.dep-wkTm-vs-ind x wp dz)

var-upclose-zero-wk-no-dep-rel :
  {Γ : Ctx} {A : Ty Γ} → (t : Tm Γ) →
  {t' : RawTm (Raw-Ctx (Γ ▸ A))} →
  Raw.WkTm {A = Raw-Ty A} (Raw-Tm t) t' →
  D.SelDepTm (Up.sel (var-upclose {Γ = Γ ▸ A} (zero {Γ = Γ} {A = A}))) t' → ⊥
var-upclose-zero-wk-no-dep-rel t wp
  (D.selected-by Raw.zero D.here dz) =
  D.dep-wkTm-vz-absurd wp dz
var-upclose-zero-wk-no-dep-rel {Γ = Γ} t wp
  (D.selected-by (Raw.succ x) (D.there-set px) dz) =
  empty-upclose-no-select {Γ = Raw-Ctx Γ} {x = x} px

var-upclose-succ-wk-no-dep-rel :
  {Γ : Ctx} {A : Ty Γ} {B : Ty (Γ ▸ A)}
  {x : Var (Γ ▸ A)} → (t : Tm (Γ ▸ A)) →
  {t' : RawTm (Raw-Ctx ((Γ ▸ A) ▸ B))} →
  Raw.WkTm {A = Raw-Ty B} (Raw-Tm t) t' →
  (tm-dep (var-upclose x) t → ⊥) →
  D.SelDepTm
    (Up.sel (var-upclose {Γ = (Γ ▸ A) ▸ B} (succ {Γ = Γ ▸ A} {A = B} x))) t' →
  ⊥
var-upclose-succ-wk-no-dep-rel {Γ = Γ} {A = A} {B = B} {x = x₀} t wp no-dep dep
  with selected-by-view
    (up-closure-sel (singleton-sel {Γ = Γ ▸ A} x₀))
    (λ x → D.DepVarTy x (Raw-Ty B))
    (λ x → dep-var-ty? x (Raw-Ty B))
    | dep
... | selected _ | D.selected-by Raw.zero D.here dz =
  D.dep-wkTm-vz-absurd wp dz
... | selected _ | D.selected-by (Raw.succ x) (D.there-set px) dz =
  no-dep (D.selected-by x px (D.dep-wkTm-vs-ind x wp dz))
... | outside _ | D.selected-by (Raw.succ x) (D.there-unset px) dz =
  no-dep (D.selected-by x px (D.dep-wkTm-vs-ind x wp dz))
```

## Inverse Image

`inv-img σ X` computes the inverse image selector on `Γ` from `σ : Sub Δ Γ`
and `X : Up Δ`. It processes the snoc structure of `Γ` via `ctx-view`: the
newest variable is set if and only if `sel-dep-tm-view X` finds a dependency of
`X` in `σ(zero)`. The selector is characterized *relationally*: `y` is selected
exactly when `D.SelDepSubAt (Up.sel X) (Raw-Sub σ) y` holds, i.e. some selected
variable of `X` depends pointwise on the image `σ(y)`. The two directions
`inv-img-selects-subat` and `inv-img-subat-selects` prove this structurally over
the explicit snoc substitution and variable (no computed lookup), and
`inv-img-upclosed` verifies the up-closure condition by pushing the
`SelDepSubAt` invariant through the head term's type with
`sel-dep-ty-sub-transitivity`. This is the live lookup-facing story: callers
should keep the relation-native `SelDepSubAt` witness instead of converting
through computed `lookup`.

```agda
{-# TERMINATING #-}
inv-img-sel :
  {Δ Γ : Ctx} → Sub Δ Γ → Up Δ → D.SelVar (Raw-Ctx Γ)
inv-img-sel {Γ = Γ} σ X with ctx-view Γ
... | ◆-view = D.sel-base
... | ▸-view {Γ = Γ′} A with σ
... | mkSub (Raw.⟨ σraw , traw ⟩)
    (⟨_,_⟩:[_]wf {A = A0} (mkSubR .σraw σwf) (mkTmR .traw twf) r)
    with sel-dep-tm-view X (mkTm traw twf)
... | selected _ = D.sel-set (Raw-Ty A) (inv-img-sel {Γ = Γ′} (mkSub σraw σwf) X)
... | outside _  = D.sel-unset (Raw-Ty A) (inv-img-sel {Γ = Γ′} (mkSub σraw σwf) X)

selects-empty : {y : Var ◆} → D.selects D.sel-base y → ⊥
selects-empty ()

inv-img-selects-subat :
  {Δ Γ : Ctx} → (σ : Sub Δ Γ) → (X : Up Δ) →
  {y : Var Γ} →
  D.selects (inv-img-sel σ X) y →
  D.SelDepSubAt (Up.sel X) (Raw-Sub σ) y
inv-img-selects-subat {Γ = Γ} σ X {y} py with ctx-view Γ
... | ◆-view = ⊥-elim (selects-empty py)
... | ▸-view {Γ = Γ′} A = inv-img-selects-subat-snoc A σ X py
  where
    inv-img-selects-subat-snoc :
      {Δ Γ : Ctx} → (A : Ty Γ) →
      (σ : Sub Δ (Γ ▸ A)) → (X : Up Δ) →
      {y : Var (Γ ▸ A)} →
      D.selects (inv-img-sel σ X) y →
      D.SelDepSubAt (Up.sel X) (Raw-Sub σ) y
    inv-img-selects-subat-snoc A
      (mkSub (Raw.⟨ σraw , traw ⟩)
        (⟨_,_⟩:[_]wf {A = A0} (mkSubR .σraw σwf) (mkTmR .traw twf) r))
      X
      {Raw.zero}
      py
      with sel-dep-tm-view X (mkTm traw twf)
    ... | selected d =
          D.selected-by
            (D.SelectedBy.selected-var d)
            (D.SelectedBy.selected-here d)
            (D.dep-sub-at-here (D.SelectedBy.selected-proof d))
    ... | outside _ with py
    ... | ()
    inv-img-selects-subat-snoc A
      (mkSub (Raw.⟨ σraw , traw ⟩)
        (⟨_,_⟩:[_]wf {A = A0} (mkSubR .σraw σwf) (mkTmR .traw twf) r))
      X
      {Raw.succ y}
      py
      with sel-dep-tm-view X (mkTm traw twf) | py
    ... | selected _ | D.there-set py′ =
          let d = inv-img-selects-subat (mkSub σraw σwf) X py′ in
          D.selected-by
            (D.SelectedBy.selected-var d)
            (D.SelectedBy.selected-here d)
            (D.dep-sub-at-there (D.SelectedBy.selected-proof d))
    ... | outside _ | D.there-unset py′ =
          let d = inv-img-selects-subat (mkSub σraw σwf) X py′ in
          D.selected-by
            (D.SelectedBy.selected-var d)
            (D.SelectedBy.selected-here d)
            (D.dep-sub-at-there (D.SelectedBy.selected-proof d))

inv-img-subat-selects :
  {Δ Γ : Ctx} → (σ : Sub Δ Γ) → (X : Up Δ) →
  {y : Var Γ} →
  D.SelDepSubAt (Up.sel X) (Raw-Sub σ) y →
  D.selects (inv-img-sel σ X) y
inv-img-subat-selects {Γ = Γ} σ X {y} dep with ctx-view Γ | y
... | ◆-view | ()
... | ▸-view {Γ = Γ′} A | y′ =
  inv-img-subat-selects-snoc A σ X {y = y′} dep
  where
    inv-img-subat-selects-snoc :
      {Δ Γ : Ctx} → (A : Ty Γ) →
      (σ : Sub Δ (Γ ▸ A)) → (X : Up Δ) →
      {y : Var (Γ ▸ A)} →
      D.SelDepSubAt (Up.sel X) (Raw-Sub σ) y →
      D.selects (inv-img-sel σ X) y
    inv-img-subat-selects-snoc A
      (mkSub (Raw.⟨ σraw , traw ⟩)
        (⟨_,_⟩:[_]wf {A = A0} (mkSubR .σraw σwf) (mkTmR .traw twf) r))
      X
      {Raw.zero}
      (D.selected-by v vsel (D.dep-sub-at-here dt))
      with sel-dep-tm-view X (mkTm traw twf)
    ... | selected _ = D.here
    ... | outside no-dep = ⊥-elim (no-dep vsel dt)
    inv-img-subat-selects-snoc A
      (mkSub (Raw.⟨ σraw , traw ⟩)
        (⟨_,_⟩:[_]wf {A = A0} (mkSubR .σraw σwf) (mkTmR .traw twf) r))
      X
      {Raw.succ y}
      (D.selected-by v vsel (D.dep-sub-at-there dat))
      with sel-dep-tm-view X (mkTm traw twf)
    ... | selected _ =
      D.there-set
        (inv-img-subat-selects (mkSub σraw σwf) X (D.selected-by v vsel dat))
    ... | outside _ =
      D.there-unset
        (inv-img-subat-selects (mkSub σraw σwf) X (D.selected-by v vsel dat))

{-# TERMINATING #-}
inv-img-upclosed :
  {Δ Γ : Ctx} → (σ : Sub Δ Γ) → (X : Up Δ) →
  is-upclosed (inv-img-sel σ X)
inv-img-upclosed {Δ = Δ} {Γ = Γ} σ X with ctx-view Γ
... | ◆-view = base
... | ▸-view {Γ = Γ′} A with σ
... | mkSub (Raw.⟨ σraw , traw ⟩)
    (⟨_,_⟩:[_]wf {A = A0} (mkSubR .σraw σwf) (mkTmR .traw twf) r)
    with sel-dep-tm-view X (mkTm traw twf)
... | selected _ =
    snoc-set
      (inv-img-sel (mkSub σraw σwf) X)
      (inv-img-upclosed (mkSub σraw σwf) X)
... | outside no-dep =
    snoc-unset
      (inv-img-sel (mkSub σraw σwf) X)
      (inv-img-upclosed (mkSub σraw σwf) X)
      indep
  where
    -- `r` is destructured here (not in the clause head) so that
    -- `inv-img-upclosed` reduces uniformly on the snoc shape: matching
    -- `typed-sub subA ht` in the head would make the function stuck on an
    -- opaque `HasTySub` variable downstream (e.g. in `3b-Naturality`).
    indep : D.SelTypeIndep (inv-img-sel (mkSub σraw σwf) X) (Raw-Ty A)
    indep {x} py dy = indep-typed py dy r
      where
        indep-typed :
          D.selects (inv-img-sel (mkSub σraw σwf) X) x →
          D.DepVarTy x (Raw-Ty A) →
          Raw.HasTySub traw (Raw-TyR A0) σraw →
          ⊥
        indep-typed py dy (Raw.typed-sub subA ht) =
          let
              dsubat = inv-img-selects-subat
                         {Δ = Δ}
                         {Γ = Γ′}
                         (mkSub σraw σwf)
                         X
                         {y = x}
                         py

              dty  = sel-dep-ty-sub-transitivity
                       {Γ = Δ}
                       {Δ = Γ′}
                       {s = Up.sel X}
                       {σ = mkSub σraw σwf}
                       {y = x}
                       {A = A}
                       dsubat subA dy

              dtm  = D.sel-dep-hasTy→tm
                       {Γ = Raw-Ctx Δ}
                       {s = Up.sel X}
                       {t = traw}
                       ht
                       dty
          in
          no-dep (D.SelectedBy.selected-here dtm) (D.SelectedBy.selected-proof dtm)

inv-img :
  {Δ Γ : Ctx} → Sub Δ Γ → Up Δ → Up Γ
inv-img σ X = mk (inv-img-sel σ X) (inv-img-upclosed σ X)

private
  mutual
    sel-dep-tm-sub-factor-raw :
      {Γ Δ : Ctx} →
      (σ : Sub Γ Δ) → (X : Up Γ) →
      {t : RawTm (Raw-Ctx Δ)} → {u : RawTm (Raw-Ctx Γ)} →
      Raw.SubstTm t (Raw-Sub σ) u →
      D.SelDepTm (Up.sel X) u →
      D.SelDepTm (inv-img-sel σ X) t
    sel-dep-tm-sub-factor-raw σ X (Raw.sub-var {x = y} p)
        (D.selected-by v vsel dv) =
      D.selected-by
        y
        (inv-img-subat-selects σ X
          (D.selected-by v vsel (D.dep-substVar→dep-sub-at p dv)))
        (D.dep-var (D.dep-var-var-refl y))
    sel-dep-tm-sub-factor-raw σ X (Raw.sub-coh p)
        (D.selected-by v vsel (D.dep-coh dυ)) =
      let d = sel-dep-sub-comp-factor-raw σ X p (D.selected-by v vsel dυ) in
      D.selected-by
        (D.SelectedBy.selected-var d)
        (D.SelectedBy.selected-here d)
        (D.dep-coh (D.SelectedBy.selected-proof d))

    sel-dep-sub-comp-factor-raw :
      {Γ Δ : Ctx} {Θ : RawCtx} →
      (σ : Sub Γ Δ) → (X : Up Γ) →
      {τ : RawSub (Raw-Ctx Δ) Θ} → {υ : RawSub (Raw-Ctx Γ) Θ} →
      Raw.CompSub τ (Raw-Sub σ) υ →
      D.SelDepSub (Up.sel X) υ →
      D.SelDepSub (inv-img-sel σ X) τ
    sel-dep-sub-comp-factor-raw σ X Raw.comp-empty (D.selected-by v vsel ())
    sel-dep-sub-comp-factor-raw σ X (Raw.comp-snoc p pt)
        (D.selected-by v vsel (D.dep-sub-here dt)) =
      let d = sel-dep-tm-sub-factor-raw σ X pt (D.selected-by v vsel dt) in
      D.selected-by
        (D.SelectedBy.selected-var d)
        (D.SelectedBy.selected-here d)
        (D.dep-sub-here (D.SelectedBy.selected-proof d))
    sel-dep-sub-comp-factor-raw σ X (Raw.comp-snoc p pt)
        (D.selected-by v vsel (D.dep-sub-there dυ)) =
      let d = sel-dep-sub-comp-factor-raw σ X p (D.selected-by v vsel dυ) in
      D.selected-by
        (D.SelectedBy.selected-var d)
        (D.SelectedBy.selected-here d)
        (D.dep-sub-there (D.SelectedBy.selected-proof d))

sel-dep-tm-sub-factor :
  {Γ Δ : Ctx} →
  (σ : Sub Γ Δ) → (X : Up Γ) →
  {t : Tm Δ} → {u : Tm Γ} →
  Raw.SubstTm (Raw-Tm t) (Raw-Sub σ) (Raw-Tm u) →
  tm-dep X u →
  D.SelDepTm (inv-img-sel σ X) (Raw-Tm t)
sel-dep-tm-sub-factor σ X p dep =
  sel-dep-tm-sub-factor-raw σ X p dep
```
