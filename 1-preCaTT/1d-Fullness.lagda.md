# 1d-Fullness: Boundaries and Fullness

This module defines the **boundary** and **fullness** conditions for
coherences in CaTT. These conditions control which coherences are valid terms.

A coherence `coh ps A u v σ` in CaTT is valid when the endpoints `u` and `v`
are **full**: their variable dependencies match the boundaries of the pasting
context `ps`. There are two flavors of fullness:

- **Compositional fullness (COMP)**: the source endpoint `u` depends on
  exactly the source-boundary variables, and the target endpoint `v` depends
  on exactly the target-boundary variables.

- **COMPCOH fullness**: both endpoints depend on every variable
  in the context.

**Boundaries** are defined at each dimension level `i`. The source boundary
`SrcBdryI Γps x i` means that variable `x` lies on the source boundary at
level `i`. The target boundary is defined analogously. The top-level wrappers
`SrcBdry` and `TgtBdry` use the top dimension `k ∸ 1`, where `k` is the
dimension index carried by the pasting-context witness `IsPsCtx Γ k`.

The keep condition `TgtKeep d z i` records when an old variable `z` is not
removed by a pasting extension `d` at level `i`: this happens either when the new
cell lives at a different dimension, or when `z` is not the specific variable
being extended.

The coverage lemma `src-bdry-i-has-dim` ensures that for every valid dimension
level `i ≤ k`, the source boundary actually contains a variable at that
dimension, returning the dimension as a relational `HasDimVar` witness.

```agda
module 1d-Fullness where

import 1a-RawSyntax as Raw
import 1b-Dependency as Dep
import 1c-Pasting as Ps

open Raw
open Ps
open Dep using (DepVarTm)

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc; _<_; _≤_; _∸_; _⊔_; z≤n; s≤s) renaming (zero to zeroℕ)
open import Data.Nat.Properties
  using (_≤?_; ≤-refl; ≤-trans; ≤-antisym; ≰⇒≥; ≰⇒>; m≥n⇒m⊔n≡m; m≤n⇒m⊔n≡n)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)
```

## Universal Quantifier over Variables

`AllVar Γ Q` asserts that a predicate `Q` holds for every variable of `Γ`. It
is used to state the fullness conditions uniformly over the entire context.

```agda
-- Universally quantified predicate over all variables of a context.
AllVar : (Γ : RawCtx) → (RawVar Γ → Set₁) → Set₁
AllVar Γ Q = ∀ (x : RawVar Γ) → Q x
```

## Proof-Relevant Source Boundary

`SrcBdryI Γps x i` is an inductive proof that variable `x` lies on the source
boundary of pasting context `Γps` at dimension level `i`. The base case
`src-ob` covers the unique object variable; `src-new-f` and `src-new-y` place
the two freshest variables on the boundary when the extension dimension `n`
falls strictly below `i`; `src-old` propagates boundary membership from the
underlying pasting context through an extension.

```agda
data SrcBdryI : ∀ {Γ : RawCtx} {k : ℕ} → IsPsCtx Γ k → RawVar Γ → ℕ → Set₁ where

  -- The unique object variable is always on the source boundary.
  src-ob : ∀ {i} → SrcBdryI isps-ob zero i

  -- In an extension, the newest edge lies on the source boundary when the
  -- extension dimension is strictly below the boundary level.
  src-new-f : ∀ {Γ : RawCtx} {k : ℕ} {x : RawVar Γ} {A : RawTy Γ} {n : ℕ}
    {Γps : IsPsCtx Γ k} {H : RawTy (Γ ▸ A)} {hext : HomTypeExt x A H}
    (d : IsDangling Γps x A n) {i} →
    n < i → SrcBdryI (isps-ext d hext) zero i

  -- The newest target also lies on the source boundary under the same
  -- dimension condition.
  src-new-y : ∀ {Γ : RawCtx} {k : ℕ} {x : RawVar Γ} {A : RawTy Γ} {n : ℕ}
    {Γps : IsPsCtx Γ k} {H : RawTy (Γ ▸ A)} {hext : HomTypeExt x A H}
    (d : IsDangling Γps x A n) {i} →
    n < i → SrcBdryI (isps-ext d hext) (succ zero) i

  -- Older source-boundary variables are preserved under extension.
  src-old : ∀ {Γ : RawCtx} {k : ℕ} {x : RawVar Γ} {A : RawTy Γ} {n : ℕ}
    {Γps : IsPsCtx Γ k} {H : RawTy (Γ ▸ A)} {hext : HomTypeExt x A H}
    (d : IsDangling Γps x A n) {z i} →
    SrcBdryI Γps z i → SrcBdryI (isps-ext d hext) (succ (succ z)) i
```

## Keep Condition for Target Boundary

`TgtKeep d z i` witnesses that the old variable `z` is not removed when
extending along the dangling variable `d` at boundary level `i`.

```agda
data TgtKeep : ∀ {Γ : RawCtx} {k : ℕ} {x : RawVar Γ} {A : RawTy Γ} {n : ℕ}
  {Γps : IsPsCtx Γ k} → IsDangling Γps x A n → RawVar Γ → ℕ → Set₁ where

  -- If the new cell lives at a different dimension, no old variable is removed.
  keep-dim-diff : ∀ {Γ : RawCtx} {k : ℕ} {x : RawVar Γ} {A : RawTy Γ} {n : ℕ}
    {Γps : IsPsCtx Γ k} (d : IsDangling Γps x A n) {z i} →
    n ≢ i → TgtKeep d z i

  -- Even at the same dimension, a variable is kept as long as it is not
  -- the specific variable consumed by the extension.
  keep-other-var : ∀ {Γ : RawCtx} {k : ℕ} {x : RawVar Γ} {A : RawTy Γ} {n : ℕ}
    {Γps : IsPsCtx Γ k} (d : IsDangling Γps x A n) {z i} →
    n ≡ i →
    z ≢ x →
    TgtKeep d z i
```

## Proof-Relevant Target Boundary

`TgtBdryI Γps x i` is the target-boundary analogue of `SrcBdryI`. The
structure mirrors the source boundary with one extra constructor: `tgt-new-y-eq`
places the newest target variable on the boundary when the extension dimension
equals `i` exactly, in addition to the strict-less-than case `tgt-new-y-lt`.
Older variables survive an extension only when `TgtKeep` confirms they are not
consumed.

```agda
data TgtBdryI : ∀ {Γ : RawCtx} {k : ℕ} → IsPsCtx Γ k → RawVar Γ → ℕ → Set₁ where

  -- The unique object variable is always on the target boundary.
  tgt-ob : ∀ {i} → TgtBdryI isps-ob zero i

  -- The newest edge is on the target boundary strictly below the level.
  tgt-new-f : ∀ {Γ : RawCtx} {k : ℕ} {x : RawVar Γ} {A : RawTy Γ} {n : ℕ}
    {Γps : IsPsCtx Γ k} {H : RawTy (Γ ▸ A)} {hext : HomTypeExt x A H}
    (d : IsDangling Γps x A n) {i} →
    n < i → TgtBdryI (isps-ext d hext) zero i

  -- The newest target is on the target boundary strictly below the level.
  tgt-new-y-lt : ∀ {Γ : RawCtx} {k : ℕ} {x : RawVar Γ} {A : RawTy Γ} {n : ℕ}
    {Γps : IsPsCtx Γ k} {H : RawTy (Γ ▸ A)} {hext : HomTypeExt x A H}
    (d : IsDangling Γps x A n) {i} →
    n < i → TgtBdryI (isps-ext d hext) (succ zero) i

  -- The newest target is also on the target boundary at the exact level.
  tgt-new-y-eq : ∀ {Γ : RawCtx} {k : ℕ} {x : RawVar Γ} {A : RawTy Γ} {n : ℕ}
    {Γps : IsPsCtx Γ k} {H : RawTy (Γ ▸ A)} {hext : HomTypeExt x A H}
    (d : IsDangling Γps x A n) {i} →
    n ≡ i → TgtBdryI (isps-ext d hext) (succ zero) i

  -- Older target-boundary variables survive when the keep condition holds.
  tgt-old : ∀ {Γ : RawCtx} {k : ℕ} {x : RawVar Γ} {A : RawTy Γ} {n : ℕ}
    {Γps : IsPsCtx Γ k} {H : RawTy (Γ ▸ A)} {hext : HomTypeExt x A H}
    (d : IsDangling Γps x A n) {z i} →
    TgtKeep d z i →
    TgtBdryI Γps z i →
    TgtBdryI (isps-ext d hext) (succ (succ z)) i
```

## Transport Lemmas

These lemmas transport `SrcBdryI` and `TgtBdryI` witnesses along a propositional
equality `e : Γ ≡ Γ'` between contexts. They are needed when the pasting
context is reconstructed in a definitionally equal but syntactically different
form. Both proofs reduce immediately to the identity case.

```agda
abstract
  src-bdry-i-transport : ∀ {Γ Γ' : RawCtx} (e : Γ ≡ Γ') {k : ℕ}
    {Γps : IsPsCtx Γ k} {x : RawVar Γ} {i} →
    SrcBdryI Γps x i →
    SrcBdryI (subst (λ Δ → IsPsCtx Δ k) e Γps) (subst RawVar e x) i
  src-bdry-i-transport refl p = p

  tgt-bdry-i-transport : ∀ {Γ Γ' : RawCtx} (e : Γ ≡ Γ') {k : ℕ}
    {Γps : IsPsCtx Γ k} {x : RawVar Γ} {i} →
    TgtBdryI Γps x i →
    TgtBdryI (subst (λ Δ → IsPsCtx Δ k) e Γps) (subst RawVar e x) i
  tgt-bdry-i-transport refl p = p
```

## Top-Level Boundary Wrappers

`SrcBdry` and `TgtBdry` are the boundary predicates used in the fullness
conditions. They fix the dimension level to `k ∸ 1`, i.e. the top dimension of
the pasting context, read directly off the `IsPsCtx Γ k` index, so callers do
not need to compute a dimension.

```agda
SrcBdry : ∀ {Γ : RawCtx} {k : ℕ} → IsPsCtx Γ k → RawVar Γ → Set₁
SrcBdry {k = k} Γps x = SrcBdryI Γps x (k ∸ 1)

TgtBdry : ∀ {Γ : RawCtx} {k : ℕ} → IsPsCtx Γ k → RawVar Γ → Set₁
TgtBdry {k = k} Γps x = TgtBdryI Γps x (k ∸ 1)
```

## Proof-Relevant Equivalence

`A ↔ B` is a record bundling maps in both directions. It is used in the COMP
fullness record to express that variable dependency and boundary membership are
in exact correspondence (not just implication in one direction).

```agda
infix 2 _↔_

record _↔_ (A B : Set₁) : Set₁ where
  field
    to : A → B
    from : B → A

open _↔_ public
```

## Fullness: COMP, COMPCOH, Full

`COMP Γps u v` requires that `u` depends on exactly the source-boundary
variables and `v` on exactly the target-boundary variables. `COMPCOH u v` instead
requires every variable to appear in both. `Full Γps u v` is the disjunction:
a coherence is valid when either condition holds.

```agda
record COMP {Γ : RawCtx} {k : ℕ} (Γps : IsPsCtx Γ k) (u v : RawTm Γ) : Set₁ where
  -- The source endpoint depends exactly on the source boundary, and the
  -- target endpoint depends exactly on the target boundary.
  field
    src-match : AllVar Γ (λ x → DepVarTm x u ↔ SrcBdry Γps x)
    tgt-match : AllVar Γ (λ x → DepVarTm x v ↔ TgtBdry Γps x)

open COMP public

COMPCOH : ∀ {Γ : RawCtx} → RawTm Γ → RawTm Γ → Set₁
-- In the COMPCOH case, every variable occurs in both endpoints.
COMPCOH {Γ} u v = AllVar Γ (λ x → DepVarTm x u × DepVarTm x v)

-- Relational positivity and endpoint witnesses for inverse coherences. These
-- replace the computed `dim-ty` / `src` / `tgt` interface, keeping this module
-- free of the computational companion: `PositiveTy A` records that `A` is at
-- least 1-dimensional, `AtLeastTwoTy A` that it is at least 2-dimensional, and
-- `HasEndpoints B s t` extracts the source/target of a hom-type relationally.
PositiveTy : ∀ {Γ : RawCtx} → RawTy Γ → Set₁
PositiveTy A = Σ ℕ (λ n → HasDimTy A (suc n))

AtLeastTwoTy : ∀ {Γ : RawCtx} → RawTy Γ → Set₁
AtLeastTwoTy A = Σ ℕ (λ n → HasDimTy A (suc (suc n)))

data HasEndpoints {Γ : RawCtx} : RawTy Γ → RawTm Γ → RawTm Γ → Set₁ where
  homEndpoints : ∀ {A : RawTy Γ} {u v : RawTm Γ} → HasEndpoints ([ A ] u ⇒ v) u v

-- Invertible cells reverse the source/target boundary dependency pattern.
record INV {Γ : RawCtx} {k : ℕ} (Γps : IsPsCtx Γ k) (u v : RawTm Γ) : Set₁ where
  field
    tgt-match : AllVar Γ (λ x → DepVarTm x u ↔ TgtBdry Γps x)
    src-match : AllVar Γ (λ x → DepVarTm x v ↔ SrcBdry Γps x)

-- Negative inverse coherences are based on the source boundary of B. The
-- endpoints `s` and `t` of `B` are recorded relationally by `endpoints`.
record INVCOH- {Γ : RawCtx} {k : ℕ} (Γps : IsPsCtx Γ k) (B : RawTy Γ) : Set₁ where
  field
    s t : RawTm Γ
    at-least-two : AtLeastTwoTy B
    endpoints : HasEndpoints B s t
    src-match : AllVar Γ (λ x → SrcBdry Γps x ↔ DepVarTm x s)
    tgt-match : AllVar Γ (λ x → SrcBdry Γps x ↔ DepVarTm x t)

-- Positive inverse coherences are based on the target boundary of B.
record INVCOH+ {Γ : RawCtx} {k : ℕ} (Γps : IsPsCtx Γ k) (B : RawTy Γ) : Set₁ where
  field
    s t : RawTm Γ
    at-least-two : AtLeastTwoTy B
    endpoints : HasEndpoints B s t
    src-match : AllVar Γ (λ x → TgtBdry Γps x ↔ DepVarTm x s)
    tgt-match : AllVar Γ (λ x → TgtBdry Γps x ↔ DepVarTm x t)

data Full {Γ : RawCtx} {k : ℕ} (Γps : IsPsCtx Γ k) (A : RawTy Γ) (u v : RawTm Γ) : Set₁ where
  -- Fullness via the compositional boundary pattern.
  full-COMP : COMP Γps u v → Full Γps A u v

  -- Fullness via the COMPCOH "depends on everything" pattern.
  full-COMPCOH : COMPCOH u v → Full Γps A u v

  -- Fullness for formally invertible positive-dimensional cells.
  full-INV : PositiveTy A → INV Γps u v → Full Γps A u v

  -- Fullness for inverse coherences directed toward a source boundary.
  full-INVCOH- : INVCOH- Γps A → Full Γps A u v

  -- Fullness for inverse coherences directed toward a target boundary.
  full-INVCOH+ : INVCOH+ Γps A → Full Γps A u v
```

### On proof-uniqueness of `Full`

Unlike the other relations of the `1-preCaTT` layer, `Full` is **not** a
proposition: `Full-uip` is false as stated, because `Full` is a genuine sum whose
cases overlap and whose payloads would need function extensionality. The full
discussion — including why `Full-uip` must remain postulated in `2a-CaTT` and how
to remove that dependency via an irrelevant field — is collected with the other
uniqueness remarks in `1z-Uniqueness`.

## Source Boundary Coverage

`src-bdry-i-has-dim` proves that for any `i ≤ k` the source boundary of an
`IsPsCtx Γ k` contains at least one variable of dimension exactly `i`, returning
the dimension as a relational `HasDimVar` witness. The proof proceeds by
induction on the pasting context: in the base case `isps-ob` only `i = 0` is
possible; in the extension case `isps-ext d` the argument splits on whether
`i ≤ k` (recurse into the underlying context) or `i` is the new top dimension
(the freshest edge variable `zero` is the witness). The extension dimension
index `(k ⊔ n) ⊔ suc n` is manipulated directly via `isDangling≤ctx`.

```agda
src-bdry-i-has-dim : ∀ {Γ : RawCtx} {k : ℕ} →
  (Γps : IsPsCtx Γ k) →
  (i : ℕ) →
  i ≤ k →
  Σ (RawVar Γ) (λ z → SrcBdryI Γps z i × HasDimVar z i)
src-bdry-i-has-dim isps-ob zeroℕ   _  = zero , src-ob , zeroDim ⋆dim
src-bdry-i-has-dim isps-ob (suc _) ()
src-bdry-i-has-dim (isps-ext {Γ = Γ} {k = k} {x = x} {A = A} {n = n} {Γps = Γps} d (hom-type-ext {A' = A'} wA)) i i≤ext
  with i ≤? k | suc n ≤? k
-- i is already realized in the underlying context: weaken the witness forward twice.
... | yes i≤k | _ =
  let r = src-bdry-i-has-dim Γps i i≤k
  in succ (succ (proj₁ r))
     , src-old d (proj₁ (proj₂ r))
     , succDim (succDim (proj₂ (proj₂ r)))
-- Impossible: the extension cannot lower the top dimension that far.
... | no i≰k | yes sucn≤k = ⊥-elim (i≰k (subst (i ≤_) ext≡k i≤ext))
  where
    ext≡k : (k ⊔ n) ⊔ suc n ≡ k
    ext≡k = trans (cong (_⊔ suc n) (m≥n⇒m⊔n≡m (isDangling≤ctx d)))
                  (m≥n⇒m⊔n≡m sucn≤k)
-- The only possible witness is the newest cell variable `f`, of dimension suc n.
... | no i≰k | no sucn≰k =
  zero , src-new-f d n<i , subst (HasDimVar zero) (sym i≡sucn) newest-dim
  where
    n<i : n < i
    n<i = ≤-trans (s≤s (isDangling≤ctx d)) (≰⇒> i≰k)

    k≤sucn : k ≤ suc n
    k≤sucn = ≰⇒≥ sucn≰k

    ext≡sucn : (k ⊔ n) ⊔ suc n ≡ suc n
    ext≡sucn = trans (cong (_⊔ suc n) (m≥n⇒m⊔n≡m (isDangling≤ctx d)))
                     (m≤n⇒m⊔n≡n k≤sucn)

    i≤sucn : i ≤ suc n
    i≤sucn = subst (i ≤_) ext≡sucn i≤ext

    i≡sucn : i ≡ suc n
    i≡sucn = ≤-antisym i≤sucn n<i

    newest-dim : HasDimVar (zero {Γ = Γ ▸ A} {A = [ A' ] vs x ⇒ vz}) (suc n)
    newest-dim = zeroDim (homDim (hasDimTy-wkTy wA (isDangling-hasDimTy d)))
```
