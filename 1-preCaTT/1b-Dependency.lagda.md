# 1b-Dependency: Variable Dependency

This module defines **semantic** dependency predicates for the raw CaTT syntax.
The key idea is that dependency is *semantic* rather than syntactic: a variable
`x` in context `Γ` depends on another variable `y` not merely when `y` appears
literally in a term involving `x`, but whenever `y` influences the *type* of
`x`.

Concretely:

- A variable `y` depends on `x` if `x = y`, or if `x` appears in the declared
  type of `y` in the context. The second case is the reason this is semantic:
  even though `y` may not mention `x` directly, changing `x` would change the
  *type* that `y` must inhabit.

- A type depends on `x` when `x` appears in its base type, source, or target.

- A term depends on `x` through its variable (via the variable dependency
  above), or through its stored substitution for coherences.

- A substitution depends on `x` when some entry in the substitution depends on
  `x`.

The dependency predicates are recorded as **inductive families** (`DepVarVar`,
`DepVarTy`, `DepVarTm`, `DepVarSubAt`, `DepVarSub`), one for each syntactic
category. This proof-relevant approach makes the dependency information directly
available for pattern matching in later constructions.

This module also defines **selectors** (`SelVar`): a selector for a context
`Γ` marks each variable as either "selected" or "unselected". The `selects`
family provides proof-relevant membership in a selector. The combination of
selectors with dependency gives rise to the notions of *selector-indexed
dependency* and *independence*, which are central to the naturality
construction.

The inductive dependency families and relation-native transfer lemmas live here.
The old computed-lookup compatibility surface has been retired; downstream code
should carry explicit substitution/lookup witnesses and use the structural
lemmas below.

```agda
module 1b-Dependency where

import 1a-RawSyntax as Raw
open Raw
open import Data.Empty using (⊥; ⊥-elim)
```

## Proof-Relevant Dependency Families

The five families `DepVarVar`, `DepVarTy`, `DepVarTm`, `DepVarSubAt`, and
`DepVarSub` are mutually inductive, each corresponding to one syntactic
category. They are defined in `Set₁` since the raw syntax families live in
`Set₁`.

`dep-var-var-refl` establishes that every variable depends on itself, which
follows by structural induction on the variable. `dep-var-vs-inv` is the
injectivity of `dep-weak`: a dependency between weakened variables comes from a
dependency between the originals. `dep-sub-at→dep-sub` forgets the codomain
position of a pointwise dependency, recording only that the substitution depends
on `x`; it is defined directly by recursion on the `DepVarSubAt` witness.

```agda
mutual

  -- Semantic dependency between variables.
  -- `succ x` depends on `zero` exactly when `x` appears in the
  -- declared type of the freshest variable.
  data DepVarVar : {Γ : RawCtx} → RawVar Γ → RawVar Γ → Set₁ where
    dep-refl : {Γ : RawCtx} {A : RawTy Γ} → DepVarVar {Γ = Γ ▸ A} zero zero
    dep-ty : {Γ : RawCtx} {A : RawTy Γ} {x : RawVar Γ} →
      DepVarTy x A → DepVarVar {Γ = Γ ▸ A} (succ x) zero
    dep-weak : {Γ : RawCtx} {A : RawTy Γ} {x y : RawVar Γ} →
      DepVarVar x y → DepVarVar {Γ = Γ ▸ A} (succ x) (succ y)

  -- Dependency of a variable in a type.
  data DepVarTy : {Γ : RawCtx} → RawVar Γ → RawTy Γ → Set₁ where
    dep-base : {Γ : RawCtx} {x : RawVar Γ} {A : RawTy Γ} {t u : RawTm Γ} →
      DepVarTy x A → DepVarTy x ([ A ] t ⇒ u)
    dep-src : {Γ : RawCtx} {x : RawVar Γ} {A : RawTy Γ} {t u : RawTm Γ} →
      DepVarTm x t → DepVarTy x ([ A ] t ⇒ u)
    dep-tgt : {Γ : RawCtx} {x : RawVar Γ} {A : RawTy Γ} {t u : RawTm Γ} →
      DepVarTm x u → DepVarTy x ([ A ] t ⇒ u)

  -- Dependency of a variable in a term.
  data DepVarTm : {Γ : RawCtx} → RawVar Γ → RawTm Γ → Set₁ where
    dep-var : {Γ : RawCtx} {x y : RawVar Γ} →
      DepVarVar x y → DepVarTm x (var y)
    dep-coh : {Γ Δ : RawCtx} {x : RawVar Γ} {A : RawTy Δ} {u v : RawTm Δ} {σ : RawSub Γ Δ} →
      DepVarSub x σ → DepVarTm x (coh A u v σ)

  -- Pointwise dependency of a substitution at a chosen codomain variable.
  data DepVarSubAt : {Γ Δ : RawCtx} → RawVar Γ → RawSub Γ Δ → RawVar Δ → Set₁ where
    dep-sub-at-here : {Γ Δ : RawCtx} {x : RawVar Γ} {σ : RawSub Γ Δ} {A : RawTy Δ} {t : RawTm Γ} →
      DepVarTm x t → DepVarSubAt {Δ = Δ ▸ A} x ⟨ σ , t ⟩ zero
    dep-sub-at-there : {Γ Δ : RawCtx} {x : RawVar Γ} {σ : RawSub Γ Δ} {A : RawTy Δ} {t : RawTm Γ} {y : RawVar Δ} →
      DepVarSubAt x σ y → DepVarSubAt {Δ = Δ ▸ A} x ⟨ σ , t ⟩ (succ y)

  -- A substitution depends on `x` if any image depends on `x`.
  data DepVarSub : {Γ Δ : RawCtx} → RawVar Γ → RawSub Γ Δ → Set₁ where
    dep-sub-here : {Γ Δ : RawCtx} {x : RawVar Γ} {σ : RawSub Γ Δ} {A : RawTy Δ} {t : RawTm Γ} →
      DepVarTm x t → DepVarSub {Δ = Δ ▸ A} x ⟨ σ , t ⟩
    dep-sub-there : {Γ Δ : RawCtx} {x : RawVar Γ} {σ : RawSub Γ Δ} {A : RawTy Δ} {t : RawTm Γ} →
      DepVarSub x σ → DepVarSub {Δ = Δ ▸ A} x ⟨ σ , t ⟩

dep-var-var-refl : {Γ : RawCtx} (x : RawVar Γ) → DepVarVar x x
dep-var-var-refl {Γ = _ Raw.▸ _} Raw.zero = dep-refl
dep-var-var-refl {Γ = _ Raw.▸ _} (Raw.succ x) = dep-weak (dep-var-var-refl x)

-- Inverse: dep-weak is injective.
dep-var-vs-inv : {Γ : RawCtx} {A : RawTy Γ} {x y : RawVar Γ} →
  DepVarVar {Γ = Γ Raw.▸ A} (Raw.succ x) (Raw.succ y) → DepVarVar x y
dep-var-vs-inv (dep-weak d) = d

-- Any pointwise dependency witnesses dependency of the whole substitution.
dep-sub-at→dep-sub : ∀ {Γ Δ : RawCtx} (x : RawVar Γ) (σ : RawSub Γ Δ) (y : RawVar Δ) →
  DepVarSubAt x σ y → DepVarSub x σ
dep-sub-at→dep-sub x (Raw.⟨ σ , t ⟩) Raw.zero (dep-sub-at-here d) = dep-sub-here d
dep-sub-at→dep-sub x (Raw.⟨ σ , t ⟩) (Raw.succ y) (dep-sub-at-there d) =
  dep-sub-there (dep-sub-at→dep-sub x σ y d)
```

## Structured Selectors

A selector `SelVar Γ` is an inductive record, mirroring the structure of `Γ`,
that marks each variable position as either **set** (selected) or **unset**
(not selected). The constructors `sel-set` and `sel-unset` both extend a
selector to a longer context: `sel-set A s` marks the newest variable as
selected, while `sel-unset A s` marks it as unselected.

The `selects` family is the proof-relevant membership predicate: `selects X x`
witnesses that variable `x` is selected by `X`.

```agda
data SelVar : RawCtx → Set₁ where
  -- In `◆`, there are no variables, so there is a unique selector
  sel-base : SelVar ◆
  -- A selector in `Γ ▸ A` is obtained from on in `Γ` by either setting
  -- or unsetting the last variable
  sel-set : {Γ : RawCtx} → (A : RawTy Γ) → SelVar Γ → SelVar (Γ ▸ A)
  sel-unset : {Γ : RawCtx} → (A : RawTy Γ) → SelVar Γ → SelVar (Γ ▸ A)

data selects : {Γ : RawCtx} → SelVar Γ → RawVar Γ → Set₁ where
  -- A selector selects the last variable iff that variable is set
  here : {Γ : RawCtx} {A : RawTy Γ} {s : SelVar Γ} → selects (sel-set A s) zero
  -- A selector selects a weakened variable in `Γ ▸ A` iff it was already selected 
  -- in `Γ`
  there-set : {Γ : RawCtx} {A : RawTy Γ} {s : SelVar Γ} {x : RawVar Γ} →
    selects s x → selects (sel-set A s) (succ x)
  there-unset : {Γ : RawCtx} {A : RawTy Γ} {s : SelVar Γ} {x : RawVar Γ} →
    selects s x → selects (sel-unset A s) (succ x)
```

## Selector-Indexed Dependency

`SelectedBy s P` is a record packaging a selected variable together with a
proof that some predicate `P` holds at that variable. It plays the role of an
existential quantifier over selected variables.

The selector-indexed dependency notions are abbreviations:
- `SelDepTy s A` — some selected variable appears in type `A`
- `SelDepTm s t` — some selected variable appears in term `t`
- `SelDepSubAt s σ y` — some selected variable appears in the image of `y` under `σ`
- `SelDepSub s σ` — some selected variable appears in some entry of `σ`

The independence notion `SelNone` quantifies universally:
- `SelNone s P` — no selected variable satisfies `P` (i.e. `P` is disjoint from `s`)

`SelTypeIndep` asserts that a type does not depend on any selected variable.

```agda
-- Selector-indexed dependency notions, defined directly.

record SelectedBy {Γ : RawCtx} (s : SelVar Γ) (P : RawVar Γ → Set₁) : Set₁ where
  constructor selected-by
  field
    selected-var : RawVar Γ
    selected-here : selects s selected-var
    selected-proof : P selected-var

SelDepTy : {Γ : RawCtx} → SelVar Γ → RawTy Γ → Set₁
SelDepTy s A = SelectedBy s (λ x → DepVarTy x A)

SelDepTm : {Γ : RawCtx} → SelVar Γ → RawTm Γ → Set₁
SelDepTm s t = SelectedBy s (λ x → DepVarTm x t)

SelDepSubAt : {Γ Δ : RawCtx} → SelVar Γ → RawSub Γ Δ → RawVar Δ → Set₁
SelDepSubAt s σ y = SelectedBy s (λ x → DepVarSubAt x σ y)

SelDepSub : {Γ Δ : RawCtx} → SelVar Γ → RawSub Γ Δ → Set₁
SelDepSub s σ = SelectedBy s (λ x → DepVarSub x σ)

-- Generic independence form over a selector.

SelNone : {Γ : RawCtx} → SelVar Γ → (RawVar Γ → Set₁) → Set₁
SelNone s P = {x : _} → selects s x → P x → ⊥

-- Independence of a type from all selected variables.

SelTypeIndep : {Γ : RawCtx} → SelVar Γ → RawTy Γ → Set₁
SelTypeIndep s A = SelNone s (λ x → DepVarTy x A)
```

## Relation-Native Dependency Transfer

The lemmas in this section move dependency information *across* the three raw
operations — weakening, substitution, and typing — working directly on the
relational witnesses (`WkTy`/`WkTm`/`WkSub`, `SubstTy`/`SubstTm`/…, `HasTy`)
rather than asking Agda to normalize a computed result. Each lemma recurses
structurally on such a witness and rebuilds the corresponding dependency proof.
Callers that used to go through computed lookup should instead keep the
corresponding `SubstVar` or `SubstTm` witness and use the pointwise lemmas in
this section.

Because types, terms, and substitutions are mutually defined, their transfer
lemmas come in mutually-recursive triples, and the names follow a fixed scheme:

- `Ty` / `Tm` / `Sub` picks the syntactic category,
- `vz` / `vs` distinguishes the fresh variable `zero` from a successor `succ x`,
- `-absurd` marks an impossibility result (the dependency cannot exist, so the
  conclusion is `⊥`),
- `-ind` marks the inductive step that carries a dependency from one side of the
  relation to the other.

The first triple handles **weakening of the fresh variable**. A weakening
`WkTy B B'` re-indexes a type `B` over `Γ` into `B'` over the extended context
`Γ ▸ A0`, shifting every existing variable up to make room for the new freshest
variable `zero`. Nothing in `B'` can therefore mention `zero`, and
`dep-wkTy-vz-absurd` (with its term and substitution companions) records exactly
this: a dependency of `zero` on a freshly weakened object is impossible.

```agda
mutual
  -- zero does not depend on relationally weakened types/terms/substitutions.
  dep-wkTy-vz-absurd : ∀ {Γ : RawCtx} {A0 B : RawTy Γ} {B' : RawTy (Γ Raw.▸ A0)}
    → Raw.WkTy {A = A0} B B'
    → DepVarTy Raw.zero B'
    → ⊥
  dep-wkTy-vz-absurd Raw.wk-⋆ ()
  dep-wkTy-vz-absurd (Raw.wk-hom p pt pu) (dep-base d) = dep-wkTy-vz-absurd p d
  dep-wkTy-vz-absurd (Raw.wk-hom p pt pu) (dep-src d) = dep-wkTm-vz-absurd pt d
  dep-wkTy-vz-absurd (Raw.wk-hom p pt pu) (dep-tgt d) = dep-wkTm-vz-absurd pu d

  dep-wkTm-vz-absurd : ∀ {Γ : RawCtx} {A0 : RawTy Γ} {t : RawTm Γ} {t' : RawTm (Γ Raw.▸ A0)}
    → Raw.WkTm {A = A0} t t'
    → DepVarTm Raw.zero t'
    → ⊥
  dep-wkTm-vz-absurd Raw.wk-var (dep-var ())
  dep-wkTm-vz-absurd (Raw.wk-coh p) (dep-coh d) = dep-wkSub-vz-absurd p d

  dep-wkSub-vz-absurd : ∀ {Γ Δ : RawCtx} {A0 : RawTy Γ}
    {σ : RawSub Γ Δ} {σ' : RawSub (Γ Raw.▸ A0) Δ}
    → Raw.WkSub {A = A0} σ σ'
    → DepVarSub Raw.zero σ'
    → ⊥
  dep-wkSub-vz-absurd Raw.wk-empty ()
  dep-wkSub-vz-absurd (Raw.wk-snoc p pt) (dep-sub-here d) = dep-wkTm-vz-absurd pt d
  dep-wkSub-vz-absurd (Raw.wk-snoc p pt) (dep-sub-there d) = dep-wkSub-vz-absurd p d
```

The second triple is the companion for a *non-fresh* variable. Weakening neither
introduces nor removes a dependency on an already-present variable, so `succ x`
depends on the weakened `B'` exactly when `x` depended on the original `B`. The
`-ind` lemmas peel the weakening off and return the dependency on the
un-weakened object.

```agda
mutual
  -- succ x depends on a relationally weakened object iff x depends on its source.
  dep-wkTy-vs-ind : ∀ {Γ : RawCtx} {A0 B : RawTy Γ} {B' : RawTy (Γ Raw.▸ A0)}
    (x : RawVar Γ)
    → Raw.WkTy {A = A0} B B'
    → DepVarTy (Raw.succ x) B'
    → DepVarTy x B
  dep-wkTy-vs-ind x Raw.wk-⋆ ()
  dep-wkTy-vs-ind x (Raw.wk-hom p pt pu) (dep-base d) = dep-base (dep-wkTy-vs-ind x p d)
  dep-wkTy-vs-ind x (Raw.wk-hom p pt pu) (dep-src d) = dep-src (dep-wkTm-vs-ind x pt d)
  dep-wkTy-vs-ind x (Raw.wk-hom p pt pu) (dep-tgt d) = dep-tgt (dep-wkTm-vs-ind x pu d)

  dep-wkTm-vs-ind : ∀ {Γ : RawCtx} {A0 : RawTy Γ} {t : RawTm Γ} {t' : RawTm (Γ Raw.▸ A0)}
    (x : RawVar Γ)
    → Raw.WkTm {A = A0} t t'
    → DepVarTm (Raw.succ x) t'
    → DepVarTm x t
  dep-wkTm-vs-ind x Raw.wk-var (dep-var d) = dep-var (dep-var-vs-inv d)
  dep-wkTm-vs-ind x (Raw.wk-coh p) (dep-coh d) = dep-coh (dep-wkSub-vs-ind x p d)

  dep-wkSub-vs-ind : ∀ {Γ Δ : RawCtx} {A0 : RawTy Γ}
    {σ : RawSub Γ Δ} {σ' : RawSub (Γ Raw.▸ A0) Δ}
    (x : RawVar Γ)
    → Raw.WkSub {A = A0} σ σ'
    → DepVarSub (Raw.succ x) σ'
    → DepVarSub x σ
  dep-wkSub-vs-ind x Raw.wk-empty ()
  dep-wkSub-vs-ind x (Raw.wk-snoc p pt) (dep-sub-here d) = dep-sub-here (dep-wkTm-vs-ind x pt d)
  dep-wkSub-vs-ind x (Raw.wk-snoc p pt) (dep-sub-there d) = dep-sub-there (dep-wkSub-vs-ind x p d)
```

The third group transfers dependency across **substitution**. When relational
substitution rewrites a `Δ`-type `A` into the `Γ`-type `B` along `σ` (and
likewise for terms, variable lookups, and substitution composition), any
dependency of a `Γ`-variable `x` on the *output* must have entered through `σ`.
Each lemma recurses on the `SubstVar` / `SubstTy` / `SubstTm` / `CompSub` witness
and turns a dependency on the result back into a dependency on `σ` itself. This
replaces the earlier approach of inverting a computed substitution.

```agda
-- Positive dependency transfer for the relational substitution evaluators.
mutual
  dep-substVar→dep-sub-at :
    ∀ {Γ Δ : RawCtx} {x : RawVar Γ} {y : RawVar Δ} {σ : RawSub Γ Δ} {t : RawTm Γ}
    → SubstVar y σ t
    → DepVarTm x t
    → DepVarSubAt x σ y
  dep-substVar→dep-sub-at sub-zero     d = dep-sub-at-here d
  dep-substVar→dep-sub-at (sub-succ p) d = dep-sub-at-there (dep-substVar→dep-sub-at p d)

  dep-substTy→dep-sub :
    ∀ {Γ Δ : RawCtx} {x : RawVar Γ} {A : RawTy Δ} {σ : RawSub Γ Δ} {B : RawTy Γ}
    → SubstTy A σ B
    → DepVarTy x B
    → DepVarSub x σ
  dep-substTy→dep-sub sub-⋆ ()
  dep-substTy→dep-sub (sub-hom pA pt pu) (dep-base d) = dep-substTy→dep-sub pA d
  dep-substTy→dep-sub (sub-hom pA pt pu) (dep-src d)  = dep-substTm→dep-sub pt d
  dep-substTy→dep-sub (sub-hom pA pt pu) (dep-tgt d)  = dep-substTm→dep-sub pu d

  dep-substTm→dep-sub :
    ∀ {Γ Δ : RawCtx} {x : RawVar Γ} {t : RawTm Δ} {σ : RawSub Γ Δ} {u : RawTm Γ}
    → SubstTm t σ u
    → DepVarTm x u
    → DepVarSub x σ
  dep-substTm→dep-sub (sub-var p) d =
    dep-sub-at→dep-sub _ _ _ (dep-substVar→dep-sub-at p d)
  dep-substTm→dep-sub (sub-coh p) (dep-coh d) = dep-compSub→dep-sub p d

  dep-compSub→dep-sub :
    ∀ {Γ Δ Θ : RawCtx} {x : RawVar Γ} {τ : RawSub Δ Θ} {σ : RawSub Γ Δ} {υ : RawSub Γ Θ}
    → CompSub τ σ υ
    → DepVarSub x υ
    → DepVarSub x σ
  dep-compSub→dep-sub comp-empty ()
  dep-compSub→dep-sub (comp-snoc p pt) (dep-sub-here d)  = dep-substTm→dep-sub pt d
  dep-compSub→dep-sub (comp-snoc p pt) (dep-sub-there d) = dep-compSub→dep-sub p d
```

The converse of `dep-substVar→dep-sub-at` reads a pointwise dependency
`DepVarSubAt x σ y` back through a `SubstVar` witness: if `σ` substitutes the
codomain variable `y` to the term `t`, then a dependency of `x` on `σ` *at* `y`
is exactly a dependency of `x` on `t`. This is the relation-native replacement
for the old computed-lookup bridge (which specialized `t` to `lookup y σ`); it
recurses structurally on the explicit snoc substitution.

```agda
dep-sub-at→dep-substVar :
  ∀ {Γ Δ : RawCtx} {x : RawVar Γ} {y : RawVar Δ} {σ : RawSub Γ Δ} {t : RawTm Γ}
  → SubstVar y σ t
  → DepVarSubAt x σ y
  → DepVarTm x t
dep-sub-at→dep-substVar sub-zero     (dep-sub-at-here d)  = d
dep-sub-at→dep-substVar (sub-succ p) (dep-sub-at-there d) = dep-sub-at→dep-substVar p d
```

Finally, the **typing bridges** connect type-level dependency to term-level
dependency through a `HasTy` witness. A variable's type is a weakening of an
earlier context type, and a coherence's type is a substitution of its head type;
in both cases a variable appearing in the *type* of a term must already appear in
the *term*. `dep-hasTyVar→dep-var` and `dep-hasTy→dep-tm` push a type dependency
down to the underlying variable or term, and `sel-dep-hasTy→tm` repackages this
for selector-indexed dependency: if some selected variable appears in `A` and `t`
has type `A`, then that variable also appears in `t`.

```agda
-- Relational typing bridge: from a HasTy witness and a type-level dependency,
-- produce the corresponding term-level dependency.
dep-hasTyVar→dep-var :
  ∀ {Γ : RawCtx} (x : RawVar Γ) {y : RawVar Γ} {A : RawTy Γ}
  → Raw.HasTyVar y A
  → DepVarTy x A
  → DepVarVar x y
dep-hasTyVar→dep-var Raw.zero (Raw.zeroTy p) d =
  ⊥-elim (dep-wkTy-vz-absurd p d)
dep-hasTyVar→dep-var (Raw.succ x) (Raw.zeroTy p) d =
  dep-ty (dep-wkTy-vs-ind x p d)
dep-hasTyVar→dep-var Raw.zero (Raw.succTy p q) d =
  ⊥-elim (dep-wkTy-vz-absurd q d)
dep-hasTyVar→dep-var (Raw.succ x) (Raw.succTy p q) d =
  dep-weak (dep-hasTyVar→dep-var x p (dep-wkTy-vs-ind x q d))

dep-hasTy→dep-tm :
  ∀ {Γ : RawCtx} (x : RawVar Γ) {t : RawTm Γ} {A : RawTy Γ}
  → Raw.HasTy t A
  → DepVarTy x A
  → DepVarTm x t
dep-hasTy→dep-tm x (Raw.varTy p) d =
  dep-var (dep-hasTyVar→dep-var x p d)
dep-hasTy→dep-tm x (Raw.cohTy p) d =
  dep-coh (dep-substTy→dep-sub p d)

sel-dep-hasTy→tm :
  ∀ {Γ : RawCtx} {s : SelVar Γ} {t : RawTm Γ} {A : RawTy Γ}
  → Raw.HasTy t A
  → SelDepTy s A
  → SelDepTm s t
sel-dep-hasTy→tm {t = t} {A = A} p d =
  selected-by
    (SelectedBy.selected-var d)
    (SelectedBy.selected-here d)
    (dep-hasTy→dep-tm (SelectedBy.selected-var d) p (SelectedBy.selected-proof d))
```
