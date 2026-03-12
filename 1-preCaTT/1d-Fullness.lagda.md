# 1d-Fullness: Boundaries and Fullness

This module defines the source/target boundary predicates for pasting contexts
and the two boolean fullness tests used later in CaTT coherence formation.

Intuitively:
- `in-src-bdry` / `in-tgt-bdry` identify which variables lie on the source or
  target boundary of a pasting context
- `check-COMP` encodes the compositional ("COMP") dependency pattern
- `check-INV` encodes the invertibility ("INV") dependency pattern
- `is-full` is their disjunction

The module also proves structural facts about dimensions and source boundaries,
especially `src-bdry-i-has-dim`, which is used in the dimension/dependency
lemmas upstream.

```agda
module 1d-Fullness where

open import Agda.Builtin.Equality
import Agda.Builtin.Sigma as Sum
import Relation.Binary.PropositionalEquality as Eq
open Eq using (trans; sym; cong; subst)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _≤_; _<_; _<ᵇ_; _∸_; _⊔_)
open import Data.Nat.Base using (_≡ᵇ_)
open import Data.Nat.Properties
  using
    (_≤?_; ≤-refl; ≤-trans; ≤-antisym; n≤1+n; n<1+n; <⇒<ᵇ; m≤m⊔n; m≤n⊔m; m≤n⇒m⊔n≡n; m≥n⇒m⊔n≡m; ⊔-lub; ≰⇒≥)
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; if_then_else_; not; _xor_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import 0a-Logic using (_iff_)

import 1a-preCaTT as Pre
open import 1a-preCaTT
open import 1b-Dep
open import 1c-Pasting
```

## Boundary Definitions (Source and Target)

The source and target boundary predicates are defined by recursion on the
pasting context. Each extension adds a new target `y` and a new cell `f`, and
the clauses below say exactly when those variables belong to the relevant
boundary at a chosen cutoff dimension.

```agda
in-src-bdry-i : ∀ {Γ} → CtxPs Γ → Var Γ → ℕ → Bool
-- In the base object context, the unique variable is always in every source boundary.
in-src-bdry-i ps-ob vz i = true
-- In an extension, `f` is in the source boundary precisely above the base dimension.
in-src-bdry-i (ps-ext xps) vz i = d <ᵇ i
  where d = dim-ty (varps-to-type xps)
-- Likewise for the new target variable `y`.
in-src-bdry-i (ps-ext xps) (vs vz) i = d <ᵇ i
  where d = dim-ty (varps-to-type xps)
-- Older variables are checked recursively in the previous pasting context.
in-src-bdry-i (ps-ext xps) (vs (vs z)) i =
  in-src-bdry-i (varps-to-ctxps xps) z i

in-tgt-bdry-i : ∀ {Γ} → CtxPs Γ → Var Γ → ℕ → Bool
-- Same base case as source boundary.
in-tgt-bdry-i ps-ob vz i = true
-- In an extension, `f` is in the target boundary precisely above the base dimension.
in-tgt-bdry-i (ps-ext xps) vz i = d <ᵇ i
  where d = dim-ty (varps-to-type xps)
-- The new target `y` is on the target boundary at the cutoff dimension.
in-tgt-bdry-i (ps-ext xps) (vs vz) i = (d <ᵇ i) ∨ (d ≡ᵇ i)
  where d = dim-ty (varps-to-type xps)
-- Older variables are usually inherited, except for one "consumed" source/target pair.
in-tgt-bdry-i (ps-ext xps) (vs (vs z)) i =
  if (d ≡ᵇ i) ∧ (var-eq z (varps-to-var xps))
  then false
  else in-tgt-bdry-i (varps-to-ctxps xps) z i
  where d = dim-ty (varps-to-type xps)

in-src-bdry : ∀ {Γ} → CtxPs Γ → Var Γ → Bool
in-src-bdry {Γ} Γps x = in-src-bdry-i Γps x (dim-ctx Γ ∸ 1)

in-tgt-bdry : ∀ {Γ} → CtxPs Γ → Var Γ → Bool
in-tgt-bdry {Γ} Γps x = in-tgt-bdry-i Γps x (dim-ctx Γ ∸ 1)

abstract
  -- Boundary predicates are stable under transport of the ambient context.
  in-src-bdry-transport :
    ∀ {Γ Γ'} (e : Γ ≡ Γ') {Γps : CtxPs Γ}
    → (x : Var Γ')
    → in-src-bdry (subst CtxPs e Γps) x
      ≡ in-src-bdry Γps (subst Var (sym e) x)
  in-src-bdry-transport refl x = refl

  in-tgt-bdry-transport :
    ∀ {Γ Γ'} (e : Γ ≡ Γ') {Γps : CtxPs Γ}
    → (x : Var Γ')
    → in-tgt-bdry (subst CtxPs e Γps) x
      ≡ in-tgt-bdry Γps (subst Var (sym e) x)
  in-tgt-bdry-transport refl x = refl
```

## Fullness Conditions (COMP and INV)

These are the two boundary/dependency patterns that later coherence formation
cares about. `COMP` says the two endpoints depend on exactly the source and
target boundaries; `INV` says both depend on everything.

```agda
check-COMP : ∀ {Γ} → CtxPs Γ → Tm Γ → Tm Γ → Bool
check-COMP {Γ} Γps u v =
  -- Every variable must match the expected source/target boundary dependency pattern.
  ∀-var Γ (λ x →
    let u-has-x = depends-on-var-tm x u
        v-has-x = depends-on-var-tm x v
        x-in-src = in-src-bdry Γps x
        x-in-tgt = in-tgt-bdry Γps x
    in (u-has-x iff x-in-src) ∧ (v-has-x iff x-in-tgt)
  )

check-INV : ∀ {Γ} → CtxPs Γ → Tm Γ → Tm Γ → Bool
check-INV {Γ} Γps u v =
  -- In the invertible case, both terms depend on every variable.
  ∀-var Γ (λ x → depends-on-var-tm x u ∧ depends-on-var-tm x v)

is-full : ∀ {Γ} → CtxPs Γ → Tm Γ → Tm Γ → Bool
-- Fullness is the disjunction of the COMP and INV patterns.
is-full Γps u v = (check-COMP Γps u v) ∨ (check-INV Γps u v)
```

## Source Boundary Coverage Proofs

The main structural fact needed downstream is that every dimension realized by
the context is represented somewhere on the source boundary. The proof is by
induction on the pasting context and splits according to whether the desired
dimension already appears in the previous stage or must be witnessed by the
newest cell.

```agda
abstract
  -- If a number fits below `suc n` but not below `n`, it must be exactly `suc n`.
  ≤-not≤-step :
    ∀ {i n : ℕ}
    → i ≤ suc n
    → ¬ (i ≤ n)
    → i ≡ suc n
  ≤-not≤-step {zero} {n} i≤ i≰n with i≰n z≤n
  ... | ()
  ≤-not≤-step {suc zero} {zero} (s≤s ≤-refl) i≰0 = refl
  ≤-not≤-step {suc (suc i)} {zero} (s≤s ()) i≰0
  ≤-not≤-step {suc i} {suc n} (s≤s i≤sn) i≰sn =
    cong suc (≤-not≤-step i≤sn (λ i≤n → i≰sn (s≤s i≤n)))

-- Every source boundary at level `i` contains a variable of dimension exactly `i`.
src-bdry-i-has-dim :
  ∀ {Γ}
  → (Γps : CtxPs Γ)
  → (i : ℕ)
  → i ≤ dim-ctx Γ
  → Sum.Σ (Var Γ)
      (λ z → Sum.Σ (in-src-bdry-i Γps z i ≡ true) (λ _ → dim-var z ≡ i))
src-bdry-i-has-dim ps-ob zero i≤ = Sum._,_ vz (Sum._,_ refl refl)
src-bdry-i-has-dim ps-ob (suc i) ()
src-bdry-i-has-dim (ps-ext {Γ = Γ} {Γps = Γps} xps) i i≤ext
  with i ≤? dim-ctx Γ | suc (dim-ty (varps-to-type xps)) ≤? dim-ctx Γ
-- If `i` is already realized in the old context, weaken the witness forward twice.
... | yes i≤Γ | _ =
  let w = src-bdry-i-has-dim Γps i i≤Γ
      z = Sum.fst w
      w' = Sum.snd w
      zInSrc = Sum.fst w'
      zDim = Sum.snd w'
  in Sum._,_ (vs (vs z))
       (Sum._,_ zInSrc
         (trans
           (dim-var-vs (vs z))
           (trans (dim-var-vs {A = varps-to-type xps} z) zDim)))
-- This branch is impossible: the extension cannot lower the ambient dimension that far.
... | no i≰Γ | yes sucd≤Γ =
  ⊥-elim (i≰Γ (≤-trans i≤ext (dim-ctx-ext≤ctx-if-sucd≤ xps sucd≤Γ)))
-- Otherwise the only possible witness is the newest cell variable `f`.
... | no i≰Γ | no sucd≰Γ =
  Sum._,_ vz (Sum._,_ src-vz-true dim-vz=i)
  where
    -- In the final branch, the ambient dimension is forced to be `suc d`, so
    -- the newest variable `f` is the only possible witness.
    d : ℕ
    d = dim-ty (varps-to-type xps)

    d≤Γ : d ≤ dim-ctx Γ
    d≤Γ = dim-varps≤dim-ctx xps

    Γ≤sucd : dim-ctx Γ ≤ suc d
    Γ≤sucd = ≰⇒≥ sucd≰Γ

    Γ≤d : dim-ctx Γ ≤ d
    Γ≤d with dim-ctx Γ ≤? d
    ... | yes Γ≤d = Γ≤d
    ... | no Γ≰d = ⊥-elim (sucd≰Γ sucd≤Γ)
      where
        Γ≡sucd : dim-ctx Γ ≡ suc d
        Γ≡sucd = ≤-not≤-step Γ≤sucd Γ≰d

        sucd≤Γ : suc d ≤ dim-ctx Γ
        sucd≤Γ rewrite sym Γ≡sucd = ≤-refl

    d≡Γ : d ≡ dim-ctx Γ
    d≡Γ = ≤-antisym d≤Γ Γ≤d

    i≤sucΓ : i ≤ suc (dim-ctx Γ)
    i≤sucΓ = ≤-trans i≤ext (dim-ctx-ext≤suc xps)

    i≡sucΓ : i ≡ suc (dim-ctx Γ)
    i≡sucΓ = ≤-not≤-step i≤sucΓ i≰Γ

    i≡sucd : i ≡ suc d
    i≡sucd = trans i≡sucΓ (sym (cong suc d≡Γ))

    src-vz-true : in-src-bdry-i (ps-ext xps) vz i ≡ true
    src-vz-true rewrite i≡sucd with d <ᵇ suc d | <⇒<ᵇ (n<1+n d)
    ... | true  | _  = refl
    ... | false | ()

    dim-vz-sucd : dim-var {Γ = ext-ctx xps} vz ≡ suc d
    dim-vz-sucd
      rewrite dim-ty-wkTy {A = hom-type-ext xps} (hom-type-ext xps)
            | dim-ty-wkTy {A = varps-to-type xps} (varps-to-type xps)
      = refl

    dim-vz=i : dim-var {Γ = ext-ctx xps} vz ≡ i
    dim-vz=i = trans dim-vz-sucd (sym i≡sucd)
```

## Test Cases

```agda
-- Source boundary ∂⁻(x,y,f) should contain only x
test-src-arrow-f : in-src-bdry test-arrow vz ≡ false
test-src-arrow-f = refl

test-src-arrow-y : in-src-bdry test-arrow (vs vz) ≡ false
test-src-arrow-y = refl

test-src-arrow-x : in-src-bdry test-arrow (vs (vs vz)) ≡ true
test-src-arrow-x = refl

-- Target boundary ∂⁺(x,y,f) should contain only y
test-tgt-arrow-f : in-tgt-bdry test-arrow vz ≡ false
test-tgt-arrow-f = refl

test-tgt-arrow-y : in-tgt-bdry test-arrow (vs vz) ≡ true
test-tgt-arrow-y = refl

test-tgt-arrow-x : in-tgt-bdry test-arrow (vs (vs vz)) ≡ false
test-tgt-arrow-x = refl
```
