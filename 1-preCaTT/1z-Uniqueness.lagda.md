# 1z-Uniqueness: Uniqueness and Proof Uniqueness

The relational operations of `1a-RawSyntax` and `1c-Pasting` have unique outputs:
fixed inputs determine the result. Their witnesses also satisfy uniqueness of
identity proofs (UIP) once those outputs are fixed as indices. The proofs of
these facts follow by a simple structural induction.

This module collects all of those uniqueness (`*-unique`) and proof-uniqueness
(`*-uip`) results in one place, away from the constructions that motivate them.
The raw-syntax facts (substitution, weakening, typing) come first, followed by
the dimension and pasting-context facts, and finally a remark on why the
analogous statement for `Full` (from `1d-Fullness`) is **false**.

```agda
module 1z-Uniqueness where

import 1a-RawSyntax as Raw
import 1c-Pasting as Ps

open Raw
open Ps

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Nat using (ℕ; suc; _⊔_)
open import Data.Nat.Properties using (≤-irrelevant)
```

## Raw substitution: uniqueness and UIP

The relational substitution operations have unique outputs: fixed inputs
determine the result.

```agda
mutual
  substVar-unique : ∀ {Γ Δ : RawCtx} {x : RawVar Δ} {σ : RawSub Γ Δ} {t t' : RawTm Γ}
    → SubstVar x σ t → SubstVar x σ t' → t ≡ t'
  substVar-unique sub-zero sub-zero = refl
  substVar-unique (sub-succ p) (sub-succ q) = substVar-unique p q

  substTy-unique : ∀ {Γ Δ : RawCtx} {A : RawTy Δ} {σ : RawSub Γ Δ} {B B' : RawTy Γ}
    → SubstTy A σ B → SubstTy A σ B' → B ≡ B'
  substTy-unique sub-⋆ sub-⋆ = refl
  substTy-unique (sub-hom pA pt pu) (sub-hom qA qt qu)
    rewrite substTy-unique pA qA
          | substTm-unique pt qt
          | substTm-unique pu qu = refl

  substTm-unique : ∀ {Γ Δ : RawCtx} {t : RawTm Δ} {σ : RawSub Γ Δ} {u u' : RawTm Γ}
    → SubstTm t σ u → SubstTm t σ u' → u ≡ u'
  substTm-unique (sub-var p) (sub-var q) = substVar-unique p q
  substTm-unique (sub-coh p) (sub-coh q)
    rewrite compSub-unique p q = refl

  compSub-unique : ∀ {Γ Δ Θ : RawCtx} {τ : RawSub Δ Θ} {σ : RawSub Γ Δ} {υ υ' : RawSub Γ Θ}
    → CompSub τ σ υ → CompSub τ σ υ' → υ ≡ υ'
  compSub-unique comp-empty comp-empty = refl
  compSub-unique (comp-snoc p pt) (comp-snoc q qt)
    rewrite compSub-unique p q
          | substTm-unique pt qt = refl

mutual
  SubstVar-uip : ∀ {Γ Δ : RawCtx} {x : RawVar Δ} {σ : RawSub Γ Δ} {t : RawTm Γ}
    → (p q : SubstVar x σ t) → p ≡ q
  SubstVar-uip sub-zero sub-zero = refl
  SubstVar-uip (sub-succ p) (sub-succ q) rewrite SubstVar-uip p q = refl

  SubstTy-uip : ∀ {Γ Δ : RawCtx} {A : RawTy Δ} {σ : RawSub Γ Δ} {B : RawTy Γ}
    → (p q : SubstTy A σ B) → p ≡ q
  SubstTy-uip sub-⋆ sub-⋆ = refl
  SubstTy-uip (sub-hom pA pt pu) (sub-hom qA qt qu)
    rewrite SubstTy-uip pA qA
          | SubstTm-uip pt qt
          | SubstTm-uip pu qu = refl

  SubstTm-uip : ∀ {Γ Δ : RawCtx} {t : RawTm Δ} {σ : RawSub Γ Δ} {u : RawTm Γ}
    → (p q : SubstTm t σ u) → p ≡ q
  SubstTm-uip (sub-var p) (sub-var q) rewrite SubstVar-uip p q = refl
  SubstTm-uip (sub-coh p) (sub-coh q) rewrite CompSub-uip p q = refl

  CompSub-uip : ∀ {Γ Δ Θ : RawCtx} {τ : RawSub Δ Θ} {σ : RawSub Γ Δ} {υ : RawSub Γ Θ}
    → (p q : CompSub τ σ υ) → p ≡ q
  CompSub-uip comp-empty comp-empty = refl
  CompSub-uip (comp-snoc p pt) (comp-snoc q qt)
    rewrite CompSub-uip p q
          | SubstTm-uip pt qt = refl
```

## Raw weakening: uniqueness and UIP

```agda
mutual
  wkTy-unique : ∀ {Γ : RawCtx} {A B : RawTy Γ} {B' B'' : RawTy (Γ ▸ A)}
    → WkTy {A = A} B B' → WkTy {A = A} B B'' → B' ≡ B''
  wkTy-unique wk-⋆ wk-⋆ = refl
  wkTy-unique (wk-hom p pt pu) (wk-hom q qt qu)
    rewrite wkTy-unique p q
          | wkTm-unique pt qt
          | wkTm-unique pu qu = refl

  wkTm-unique : ∀ {Γ : RawCtx} {A : RawTy Γ} {t : RawTm Γ} {t' t'' : RawTm (Γ ▸ A)}
    → WkTm {A = A} t t' → WkTm {A = A} t t'' → t' ≡ t''
  wkTm-unique wk-var wk-var = refl
  wkTm-unique (wk-coh p) (wk-coh q) rewrite wkSub-unique p q = refl

  wkSub-unique : ∀ {Γ Δ : RawCtx} {A : RawTy Γ} {σ : RawSub Γ Δ}
    {σ' σ'' : RawSub (Γ ▸ A) Δ}
    → WkSub {A = A} σ σ' → WkSub {A = A} σ σ'' → σ' ≡ σ''
  wkSub-unique wk-empty wk-empty = refl
  wkSub-unique (wk-snoc p pt) (wk-snoc q qt)
    rewrite wkSub-unique p q
          | wkTm-unique pt qt = refl

mutual
  WkTy-uip : ∀ {Γ : RawCtx} {A B : RawTy Γ} {B' : RawTy (Γ ▸ A)}
    → (p q : WkTy {A = A} B B') → p ≡ q
  WkTy-uip wk-⋆ wk-⋆ = refl
  WkTy-uip (wk-hom p pt pu) (wk-hom q qt qu)
    rewrite WkTy-uip p q
          | WkTm-uip pt qt
          | WkTm-uip pu qu = refl

  WkTm-uip : ∀ {Γ : RawCtx} {A : RawTy Γ} {t : RawTm Γ} {t' : RawTm (Γ ▸ A)}
    → (p q : WkTm {A = A} t t') → p ≡ q
  WkTm-uip wk-var wk-var = refl
  WkTm-uip (wk-coh p) (wk-coh q) rewrite WkSub-uip p q = refl

  WkSub-uip : ∀ {Γ Δ : RawCtx} {A : RawTy Γ} {σ : RawSub Γ Δ}
    {σ' : RawSub (Γ ▸ A) Δ}
    → (p q : WkSub {A = A} σ σ') → p ≡ q
  WkSub-uip wk-empty wk-empty = refl
  WkSub-uip (wk-snoc p pt) (wk-snoc q qt)
    rewrite WkSub-uip p q
          | WkTm-uip pt qt = refl
```

## Raw typing: uniqueness and UIP

```agda
hasTyVar-unique : ∀ {Γ : RawCtx} {x : RawVar Γ} {A B : RawTy Γ}
  → HasTyVar x A
  → HasTyVar x B
  → A ≡ B
hasTyVar-unique (zeroTy p) (zeroTy q) = wkTy-unique p q
hasTyVar-unique (succTy p p') (succTy q q')
  rewrite hasTyVar-unique p q = wkTy-unique p' q'

hasTy-unique : ∀ {Γ : RawCtx} {t : RawTm Γ} {A B : RawTy Γ}
  → HasTy t A
  → HasTy t B
  → A ≡ B
hasTy-unique (varTy p) (varTy q) = hasTyVar-unique p q
hasTy-unique (cohTy p) (cohTy q) = substTy-unique p q

HasTyVar-uip : ∀ {Γ : RawCtx} {x : RawVar Γ} {A : RawTy Γ}
  → (p q : HasTyVar x A)
  → p ≡ q
HasTyVar-uip (zeroTy p) (zeroTy q)
  rewrite WkTy-uip p q = refl
HasTyVar-uip (succTy p p') (succTy q q')
  with hasTyVar-unique p q
... | refl
  rewrite HasTyVar-uip p q
        | WkTy-uip p' q' = refl

HasTy-uip : ∀ {Γ : RawCtx} {t : RawTm Γ} {A : RawTy Γ}
  → (p q : HasTy t A)
  → p ≡ q
HasTy-uip (varTy p) (varTy q)
  rewrite HasTyVar-uip p q = refl
HasTy-uip (cohTy p) (cohTy q)
  rewrite SubstTy-uip p q = refl

HasTySub-uip : ∀ {Γ Δ : RawCtx} {t : RawTm Γ} {A : RawTy Δ} {σ : RawSub Γ Δ}
  → (p q : HasTySub t A σ) → p ≡ q
HasTySub-uip (typed-sub s h) (typed-sub s' h')
  with substTy-unique s s'
... | refl rewrite SubstTy-uip s s' | HasTy-uip h h' = refl
```

## Dimensions: uniqueness

Each of the three dimension assignments picks out a single numeral.

```agda
hasDimTy-unique : ∀ {Γ : RawCtx} {A : RawTy Γ} {n m : ℕ} →
  HasDimTy A n → HasDimTy A m → n ≡ m
hasDimTy-unique ⋆dim       ⋆dim       = refl
hasDimTy-unique (homDim p) (homDim q) = cong suc (hasDimTy-unique p q)

hasDimCtx-unique : ∀ {Γ : RawCtx} {n m : ℕ} →
  HasDimCtx Γ n → HasDimCtx Γ m → n ≡ m
hasDimCtx-unique ◆dim          ◆dim          = refl
hasDimCtx-unique (snocDim p p') (snocDim q q') =
  cong₂ _⊔_ (hasDimCtx-unique p q) (hasDimTy-unique p' q')

hasDimVar-unique : ∀ {Γ : RawCtx} {x : RawVar Γ} {n m : ℕ} →
  HasDimVar x n → HasDimVar x m → n ≡ m
hasDimVar-unique (zeroDim p) (zeroDim q) = hasDimTy-unique p q
hasDimVar-unique (succDim p) (succDim q) = hasDimVar-unique p q
```

## Extension witnesses: uniqueness and UIP

The two extension-witness relations have unique outputs and satisfy UIP. `WkTy²`
first reconciles its hidden intermediate type via `wkTy-unique` before appealing
to the single-step lemmas.

```agda
homTypeExt-unique : ∀ {Γ : RawCtx} {x : RawVar Γ} {A : RawTy Γ}
  {H H' : RawTy (Γ ▸ A)} →
  HomTypeExt x A H → HomTypeExt x A H' → H ≡ H'
homTypeExt-unique (hom-type-ext p) (hom-type-ext q)
  rewrite wkTy-unique p q = refl

HomTypeExt-uip : ∀ {Γ : RawCtx} {x : RawVar Γ} {A : RawTy Γ}
  {H : RawTy (Γ ▸ A)} →
  (p q : HomTypeExt x A H) → p ≡ q
HomTypeExt-uip (hom-type-ext p) (hom-type-ext q)
  rewrite WkTy-uip p q = refl

wkTy²-unique : ∀ {Γ : RawCtx} {A : RawTy Γ} {C : RawTy (Γ ▸ A)}
  {B : RawTy Γ} {D D' : RawTy ((Γ ▸ A) ▸ C)} →
  WkTy² {A = A} {C = C} B D → WkTy² {A = A} {C = C} B D' → D ≡ D'
wkTy²-unique (wk² wa wh) (wk² wa' wh')
  with wkTy-unique wa wa'
... | refl = wkTy-unique wh wh'

WkTy²-uip : ∀ {Γ : RawCtx} {A : RawTy Γ} {C : RawTy (Γ ▸ A)}
  {B : RawTy Γ} {D : RawTy ((Γ ▸ A) ▸ C)} →
  (p q : WkTy² {A = A} {C = C} B D) → p ≡ q
WkTy²-uip (wk² wa wh) (wk² wa' wh')
  with wkTy-unique wa wa'
... | refl rewrite WkTy-uip wa wa' | WkTy-uip wh wh' = refl
```

## Pasting contexts and dangling variables: uniqueness and UIP

The dimension index of a pasting context is unique, as it is just the dimension
of the underlying context.

```agda
isPsCtx-dim-unique : ∀ {Γ : RawCtx} {k k' : ℕ} →
  IsPsCtx Γ k → IsPsCtx Γ k' → k ≡ k'
isPsCtx-dim-unique p q =
  hasDimCtx-unique (isPsCtx-hasDimCtx p) (isPsCtx-hasDimCtx q)
```

A dangling variable determines its own type and dimension: any two dangling
witnesses for the *same* variable record the same declared type (because typing
of a variable is unique, `hasTyVar-unique`) and the same dimension.

```agda
isDangling-ty-unique : ∀ {Γ : RawCtx} {k : ℕ} {Γps : IsPsCtx Γ k}
  {x : RawVar Γ} {A A' : RawTy Γ} {n n' : ℕ} →
  IsDangling Γps x A n → IsDangling Γps x A' n' → A ≡ A'
isDangling-ty-unique d d' =
  hasTyVar-unique (isDangling-hasTyVar d) (isDangling-hasTyVar d')

isDangling-dim-unique : ∀ {Γ : RawCtx} {k : ℕ} {Γps : IsPsCtx Γ k}
  {x : RawVar Γ} {A : RawTy Γ} {n n' : ℕ} →
  IsDangling Γps x A n → IsDangling Γps x A n' → n ≡ n'
isDangling-dim-unique d d' =
  hasDimTy-unique (isDangling-hasDimTy d) (isDangling-hasDimTy d')
```

Finally, the two mutually-defined families satisfy UIP. `IsDangling-uip` recurses
only on itself: in each constructor the underlying pasting context (`Γps`, hence
`d` and `hext`) is forced by the index, so only the stored weakening witnesses and
the strict-inequality side condition can differ — handled by `WkTy-uip` /
`WkTy²-uip` and `≤-irrelevant`. The `dangling-weak` case additionally reconciles
the persisting variable's type via `isDangling-ty-unique` before recursing.

```agda
IsDangling-uip : ∀ {Γ : RawCtx} {k : ℕ} {Γps : IsPsCtx Γ k}
  {x : RawVar Γ} {A : RawTy Γ} {n : ℕ} →
  (p q : IsDangling Γps x A n) → p ≡ q
IsDangling-uip dangling-ob dangling-ob = refl
IsDangling-uip (dangling-f d hext w) (dangling-f _ _ w')
  rewrite WkTy-uip w w' = refl
IsDangling-uip (dangling-y d hext w2) (dangling-y _ _ w2')
  rewrite WkTy²-uip w2 w2' = refl
IsDangling-uip (dangling-weak d e hext w2 lt) (dangling-weak _ e' _ w2' lt')
  with isDangling-ty-unique e e'
... | refl
  rewrite IsDangling-uip e e' | WkTy²-uip w2 w2' | ≤-irrelevant lt lt' = refl
```

`IsPsCtx-uip` cannot be proved by matching both arguments directly: once the first
`isps-ext` fixes the dimension index to the non-injective expression
`(k ⊔ n) ⊔ suc n`, Agda gets stuck unifying the second extension against it. We
therefore route through a heterogeneous helper `IsPsCtx-uip-het` that keeps the
two dimensions as *independent* indices joined by an explicit equation `e : k ≡ k'`,
so each `isps-ext` is matched with its index still free. The helper then unifies
the existential dimension (`hasDimTy-unique`) and sub-context dimension
(`isPsCtx-dim-unique`), recurses on the sub-context, discharges the stored
witnesses via `IsDangling-uip` / `WkTy-uip`, and collapses `e` to `refl`. The
public `IsPsCtx-uip` is the diagonal `e = refl` instance.

```agda
IsPsCtx-uip-het : ∀ {Γ : RawCtx} {k k' : ℕ}
  (p : IsPsCtx Γ k) (q : IsPsCtx Γ k') (e : k ≡ k') →
  subst (IsPsCtx Γ) e p ≡ q
IsPsCtx-uip-het isps-ob isps-ob refl = refl
IsPsCtx-uip-het (isps-ext {Γps = Γps}  d  (hom-type-ext wA))
                (isps-ext {Γps = Γps'} d' (hom-type-ext wA')) e
  with hasDimTy-unique (isDangling-hasDimTy d) (isDangling-hasDimTy d')
... | refl
  with isPsCtx-dim-unique Γps Γps'
... | refl
  with IsPsCtx-uip-het Γps Γps' refl
... | refl
  with e
... | refl rewrite IsDangling-uip d d' | WkTy-uip wA wA' = refl

IsPsCtx-uip : ∀ {Γ : RawCtx} {k : ℕ} → (p q : IsPsCtx Γ k) → p ≡ q
IsPsCtx-uip p q = IsPsCtx-uip-het p q refl
```

## On proof-uniqueness of `Full`

The well-formedness layer in `2a-CaTT` would like `Full` (defined in
`1d-Fullness`) to be a *proposition* (`Full-uip : (p q : Full Γps A u v) → p ≡ q`),
so that two well-formedness proofs of the same raw coherence are equal. **This is
not provable — indeed it is false as stated** — for two independent reasons:

1. **`Full` is a genuine sum whose cases overlap.** Distinct constructors of a
   data type are never propositionally equal, so `Full-uip` can only hold if at
   most one constructor ever applies. But the cases are not mutually exclusive.
   Concretely, over the object pasting context `isps-ob` the whole context is its
   own source and target boundary (`src-ob` / `tgt-ob`), so
   `Full isps-ob ⋆ (var zero) (var zero)` is inhabited by **both**
   `full-COMP _` (the single variable depends on exactly the boundary) and
   `full-COMPCOH _` (it depends on everything). These two witnesses are unequal.

2. **The payloads need function extensionality.** Even restricted to a single
   constructor, `COMP` / `INV` / `INVCOH±` store `AllVar`-indexed families of
   `↔`-records, i.e. Π-types into pairs of functions. Proving two such payloads
   equal requires funext, which this development does not assume.

Consequently `Full-uip` remains **postulated** in `2a-CaTT`. The sound way to
remove that postulate is not to prove it but to stop depending on it: make the
fullness component of the `coh-wf` constructor an *irrelevant* field (Agda's `.`
irrelevance), so any two fullness witnesses are definitionally equal and the
coherence case of `Tm-iswf-uip` needs no `Full-uip` at all. That is a change to
the `2a-CaTT` well-formedness datatype rather than something provable here.
