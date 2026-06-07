# 1c-Pasting: Dimensions and Pasting Contexts

This module equips the raw syntax with two closely related notions: dimensions
and pasting contexts.

**Dimension** is a numerical measure of the cell-level of a type or variable.
The type `⋆` has dimension 0; a hom-type `[ A ] t ⇒ u` has dimension
`1 + dim(A)`. The dimension of a context is the maximum dimension of its
declared types.

In this version the primary interface is **inductive and relational**:

- `HasDimTy A n` — "the type `A` has dimension `n`",
- `HasDimCtx Γ n` — "the context `Γ` has dimension `n`",
- `HasDimVar x n` — "the variable `x` has dimension `n`",
- `IsPsCtx Γ k` — "`Γ` is a pasting context of dimension `k`",
- `IsDangling Γps x A n` — "`x : A` is dangling in `Γps`, with dimension `n`".

The natural-number comparisons themselves (`m < n`, `m ≤ n`, `m ≡ n`) remain
ordinary arithmetic; only the *dimension assignments* are relationalised.

**Pasting contexts** are the composable cell-shapes of CaTT. A pasting context
is built inductively from the single-object context `(x : ⋆)` by repeatedly
choosing a **dangling variable** `x : A` and extending the context by:
- a new target variable `y : A` (same type as `x`), and
- a new arrow/cell `f : [ A ] x ⇒ y`.

The key rule is that a previously dangling variable of *strictly lower*
dimension remains dangling after such an extension. This is encoded by the
`dangling-weak` constructor.

Crucially, this module is now **purely relational**: it imports only the
relational core `1a-RawSyntax`, never the computational companion. The weakened
types that appear in pasting extensions (the new cell type `[ wkTy A ] x ⇒ y`,
and the weakened declared types of the persisting variables) are no longer
*computed*. Instead the constructors **carry weakening evidence** — `WkTy`,
`WkTy²`, and the extension-cell relation `HomTypeExt` — recording *which*
weakened type is used. The legacy computed functions (`dim-ty`, `dim-ctx`,
`dim-var`, `src`, `tgt`, `desuspend`) are no longer part of the live
proposition-facing API; callers should use the relational dimension and
extension witnesses directly.

This module only inspects the `⋆` and `[_]_⇒_` constructors of types,
and uses `var` and weakening for terms. It does not depend on `coh`.

```agda
module 1c-Pasting where

import 1a-RawSyntax as Raw
open Raw
open import Data.Nat using (ℕ; suc; _<_; _≤_; _⊔_; s≤s; z≤n) renaming (zero to zeroℕ)
open import Data.Nat.Properties
  using
    ( ≤-refl
    ; ≤-trans
    ; m≤m⊔n
    ; m≤n⊔m
    ; m≤n⇒m⊔n≡n
    ; m≥n⇒m⊔n≡m
    ; ⊔-lub
    ; n≤1+n
    ; ≤-irrelevant
    )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂; subst)
```

## Relational Dimensions

`HasDimTy`, `HasDimCtx`, and `HasDimVar` assign dimensions inductively. A type's
dimension counts the hom-layers above `⋆`; a context's dimension is the maximum
over its declared types; a variable's dimension is the dimension of its declared
type. Because weakening does not change dimension, the variable rules read off
the dimension of the *unweakened* declared type.

```agda
data HasDimTy : ∀ {Γ : RawCtx} → RawTy Γ → ℕ → Set₁ where
  -- dim(⋆) = 0
  ⋆dim   : ∀ {Γ : RawCtx} → HasDimTy {Γ} ⋆ 0
  -- dim([ A ] t ⇒ u) = dim(A) + 1
  homDim : ∀ {Γ : RawCtx} {A : RawTy Γ} {t u : RawTm Γ} {n : ℕ} →
    HasDimTy A n → HasDimTy ([ A ] t ⇒ u) (suc n)

data HasDimCtx : RawCtx → ℕ → Set₁ where
  -- dim(◆) = 0
  ◆dim    : HasDimCtx ◆ 0
  -- dim(Γ ▸ A) = max(dim(Γ), dim(A))
  snocDim : ∀ {Γ : RawCtx} {A : RawTy Γ} {n m : ℕ} →
    HasDimCtx Γ n → HasDimTy A m → HasDimCtx (Γ ▸ A) (n ⊔ m)

data HasDimVar : ∀ {Γ : RawCtx} → RawVar Γ → ℕ → Set₁ where
  -- dim(zero : A) = dim(A)
  zeroDim : ∀ {Γ : RawCtx} {A : RawTy Γ} {n : ℕ} →
    HasDimTy A n → HasDimVar (zero {Γ = Γ} {A = A}) n
  -- dim(succ x) = dim(x)   (weakening preserves dimension)
  succDim : ∀ {Γ : RawCtx} {A : RawTy Γ} {x : RawVar Γ} {n : ℕ} →
    HasDimVar x n → HasDimVar (succ {A = A} x) n
```

Dimension is preserved by weakening and substitution: the proofs are structural
inductions on the `HasDimTy` witness, consuming the relational `WkTy`/`SubstTy`
evidence rather than a computed output.

```agda
hasDimTy-wkTy : ∀ {Γ : RawCtx} {A B : RawTy Γ} {B' : RawTy (Γ ▸ A)} {n : ℕ} →
  WkTy {A = A} B B' → HasDimTy B n → HasDimTy B' n
hasDimTy-wkTy wk-⋆             ⋆dim       = ⋆dim
hasDimTy-wkTy (wk-hom p pt pu) (homDim q) = homDim (hasDimTy-wkTy p q)

hasDimTy-sub : ∀ {Γ Δ : RawCtx} {A : RawTy Γ} {σ : RawSub Δ Γ}
  {B : RawTy Δ} {n : ℕ} →
  SubstTy A σ B → HasDimTy A n → HasDimTy B n
hasDimTy-sub sub-⋆               ⋆dim       = ⋆dim
hasDimTy-sub (sub-hom p pt pu) (homDim q) = homDim (hasDimTy-sub p q)
```

Each of these relations also assigns a *unique* numeral to a fixed input; those
uniqueness proofs are collected in `1z-Uniqueness`, away from the constructions
that motivate them.

## Extension Witnesses

Two small relations record the weakened types used by a pasting extension,
without computing them.

`HomTypeExt x A H` says that `H` is the type of the new extension cell over a
dangling variable `x : A`: it is a hom-type `[ A' ] vs x ⇒ vz` whose base `A'`
is the weakening of `A` across the freshly bound copy of `A`. The witness stores
the `WkTy A A'` evidence.

`WkTy² B B''` records two successive weakenings, `WkTy B B'` followed by
`WkTy B' B''`. It keeps the dangling constructors (which weaken older declared
types across *two* new binders) readable.

```agda
data HomTypeExt {Γ : RawCtx} (x : RawVar Γ) (A : RawTy Γ)
  : RawTy (Γ ▸ A) → Set₁ where
  hom-type-ext : ∀ {A' : RawTy (Γ ▸ A)}
    → WkTy {A = A} A A'
    → HomTypeExt x A ([ A' ] vs x ⇒ vz)

data WkTy² {Γ : RawCtx} {A : RawTy Γ} {C : RawTy (Γ ▸ A)}
  : RawTy Γ → RawTy ((Γ ▸ A) ▸ C) → Set₁ where
  wk² : ∀ {B : RawTy Γ} {B' : RawTy (Γ ▸ A)} {B'' : RawTy ((Γ ▸ A) ▸ C)}
    → WkTy {A = A} B B'
    → WkTy {A = C} B' B''
    → WkTy² B B''
```

Both `HomTypeExt` and `WkTy²` have unique outputs and satisfy UIP; those proofs
live in `1z-Uniqueness`.

## Pasting Contexts

`IsPsCtx Γ k` says that `Γ` is a pasting context of dimension `k`, and
`IsDangling Γps x A n` picks out a dangling variable `x : A` of dimension `n` in
the pasting context `Γps`. The two families are mutually inductive and carry
their dimensions as indices, so dimensional side-conditions are stated as plain
arithmetic on those indices rather than as computations on the raw syntax.

The extension constructor `isps-ext` now carries an explicit extension-cell type
`H` together with a `HomTypeExt x A H` witness; the extended raw context is then
the plain syntactic `(Γ ▸ A) ▸ H`. The four dangling constructors are:
- `dangling-ob` — the unique dangling variable in `(x : ⋆)`,
- `dangling-f` — the new cell `f` is dangling in any extension; it carries the
  `WkTy H H'` witness for the weakening of the cell type across its own binder,
- `dangling-y` — the new target `y` is also dangling; it carries a `WkTy²`
  witness for the double weakening of `A`,
- `dangling-weak` — an older dangling variable of strictly smaller dimension
  persists after extension; it carries a `WkTy²` witness for its weakened type.

The context-dimension index of an extension is written in the *unsimplified*
form `(k ⊔ n) ⊔ suc n`, matching the two raw context extensions directly.

```agda
mutual
  -- `IsPsCtx Γ k` means "Γ is a pasting context of dimension k".
  data IsPsCtx : RawCtx → ℕ → Set₁

  -- `IsDangling Γps x A n` means "x : A is dangling in Γps, of dimension n".
  data IsDangling :
    ∀ {Γ : RawCtx} {k : ℕ} → IsPsCtx Γ k → RawVar Γ → RawTy Γ → ℕ → Set₁

  data IsPsCtx where
    -- Base pasting context: a single object.
    isps-ob : IsPsCtx (◆ ▸ ⋆) 0
    -- Extend a pasting context along a chosen dangling variable, by a new cell
    -- of type `H` (with `HomTypeExt` evidence).
    isps-ext : ∀ {Γ : RawCtx} {k : ℕ} {x : RawVar Γ} {A : RawTy Γ} {n : ℕ}
      {Γps : IsPsCtx Γ k} {H : RawTy (Γ ▸ A)} →
      (d : IsDangling Γps x A n) →
      HomTypeExt x A H →
      IsPsCtx ((Γ ▸ A) ▸ H) ((k ⊔ n) ⊔ suc n)

  data IsDangling where
    -- In `(x : ⋆)`, the unique dangling variable is `x`.
    dangling-ob : IsDangling isps-ob zero ⋆ 0

    -- In an extension, the new cell `f` is dangling, one dimension higher. Its
    -- type is the weakening `H'` of the cell type `H` across its own binder.
    dangling-f : ∀ {Γ : RawCtx} {k : ℕ} {x : RawVar Γ} {A : RawTy Γ} {n : ℕ}
      {Γps : IsPsCtx Γ k} {H : RawTy (Γ ▸ A)} {H' : RawTy ((Γ ▸ A) ▸ H)} →
      (d : IsDangling Γps x A n) →
      (hext : HomTypeExt x A H) →
      WkTy {A = H} H H' →
      IsDangling (isps-ext d hext) zero H' (suc n)

    -- The new target `y` is also dangling, at the same dimension as `x`. Its
    -- type is `A` weakened across the two new binders.
    dangling-y : ∀ {Γ : RawCtx} {k : ℕ} {x : RawVar Γ} {A : RawTy Γ} {n : ℕ}
      {Γps : IsPsCtx Γ k} {H : RawTy (Γ ▸ A)} {A'' : RawTy ((Γ ▸ A) ▸ H)} →
      (d : IsDangling Γps x A n) →
      (hext : HomTypeExt x A H) →
      WkTy² {A = A} {C = H} A A'' →
      IsDangling (isps-ext d hext) (succ zero) A'' n

    -- Older dangling variables persist if their dimension is strictly smaller;
    -- their type is weakened across the two new binders.
    dangling-weak : ∀ {Γ : RawCtx} {k : ℕ} {x : RawVar Γ} {A : RawTy Γ} {n : ℕ}
      {z : RawVar Γ} {B : RawTy Γ} {m : ℕ} {Γps : IsPsCtx Γ k}
      {H : RawTy (Γ ▸ A)} {B'' : RawTy ((Γ ▸ A) ▸ H)} →
      (d : IsDangling Γps x A n) →
      (e : IsDangling Γps z B m) →
      (hext : HomTypeExt x A H) →
      WkTy² {A = A} {C = H} B B'' →
      m < n →
      IsDangling (isps-ext d hext) (succ (succ z)) B'' m
```

## Positive Structural Lemmas

These lemmas read typing and dimension data directly off an `IsDangling` /
`IsPsCtx` witness, by induction on its constructors. They consume the weakening
evidence stored in the constructors directly, never recomputing it.

First: a dangling variable is well-typed at its recorded type.

```agda
isDangling-hasTyVar : ∀ {Γ : RawCtx} {k : ℕ} {Γps : IsPsCtx Γ k}
  {x : RawVar Γ} {A : RawTy Γ} {n : ℕ} →
  IsDangling Γps x A n → HasTyVar x A
isDangling-hasTyVar dangling-ob                       = zeroTy wk-⋆
isDangling-hasTyVar (dangling-f d hext w)             = zeroTy w
isDangling-hasTyVar (dangling-y d hext (wk² wa wh))   = succTy (zeroTy wa) wh
isDangling-hasTyVar (dangling-weak d e hext (wk² wa wh) _) =
  succTy (succTy (isDangling-hasTyVar e) wa) wh
```

Next: a dangling variable's recorded type has its recorded dimension, and hence
so does the variable.

```agda
isDangling-hasDimTy : ∀ {Γ : RawCtx} {k : ℕ} {Γps : IsPsCtx Γ k}
  {x : RawVar Γ} {A : RawTy Γ} {n : ℕ} →
  IsDangling Γps x A n → HasDimTy A n
isDangling-hasDimTy dangling-ob = ⋆dim
isDangling-hasDimTy (dangling-f d (hom-type-ext wA) w) =
  hasDimTy-wkTy w (homDim (hasDimTy-wkTy wA (isDangling-hasDimTy d)))
isDangling-hasDimTy (dangling-y d hext (wk² wa wh)) =
  hasDimTy-wkTy wh (hasDimTy-wkTy wa (isDangling-hasDimTy d))
isDangling-hasDimTy (dangling-weak d e hext (wk² wa wh) _) =
  hasDimTy-wkTy wh (hasDimTy-wkTy wa (isDangling-hasDimTy e))

isDangling-hasDimVar : ∀ {Γ : RawCtx} {k : ℕ} {Γps : IsPsCtx Γ k}
  {x : RawVar Γ} {A : RawTy Γ} {n : ℕ} →
  IsDangling Γps x A n → HasDimVar x n
isDangling-hasDimVar dangling-ob = zeroDim ⋆dim
isDangling-hasDimVar (dangling-f d (hom-type-ext wA) w) =
  zeroDim (homDim (hasDimTy-wkTy wA (isDangling-hasDimTy d)))
isDangling-hasDimVar (dangling-y d hext w2)       = succDim (zeroDim (isDangling-hasDimTy d))
isDangling-hasDimVar (dangling-weak d e hext w2 _) = succDim (succDim (isDangling-hasDimVar e))
```

A pasting context has its recorded dimension. The extension case extends the
underlying `HasDimCtx` twice: once by the dangling type `A : n`, then by the new
cell type `H : suc n`.

```agda
isPsCtx-hasDimCtx : ∀ {Γ : RawCtx} {k : ℕ} → IsPsCtx Γ k → HasDimCtx Γ k
isPsCtx-hasDimCtx isps-ob = snocDim ◆dim ⋆dim
isPsCtx-hasDimCtx (isps-ext {Γps = Γps} d (hom-type-ext wA)) =
  snocDim (snocDim (isPsCtx-hasDimCtx Γps) (isDangling-hasDimTy d))
          (homDim (hasDimTy-wkTy wA (isDangling-hasDimTy d)))
```

Every dangling variable lives within the ambient context dimension. This is the
relational replacement for the old `dim-varps≤dim-ctx`.

```agda
isDangling≤ctx : ∀ {Γ : RawCtx} {k : ℕ} {Γps : IsPsCtx Γ k}
  {x : RawVar Γ} {A : RawTy Γ} {n : ℕ} →
  IsDangling {k = k} Γps x A n → n ≤ k
isDangling≤ctx dangling-ob                = z≤n
isDangling≤ctx (dangling-f {k = k} {n = n} d hext w) =
  m≤n⊔m (k ⊔ n) (suc n)
isDangling≤ctx (dangling-y {k = k} {n = n} d hext w2) =
  ≤-trans (n≤1+n n) (m≤n⊔m (k ⊔ n) (suc n))
isDangling≤ctx (dangling-weak {k = k} {n = n} d e hext w2 _) =
  ≤-trans (≤-trans (isDangling≤ctx e) (m≤m⊔n k n)) (m≤m⊔n (k ⊔ n) (suc n))
```

## Legacy `CtxPs` / `VarPs` Surface (intentionally omitted)

The pre-migration code exposed an unindexed `CtxPs Γ` / `VarPs Γ Γps` core with
projections `varps-to-var`, `varps-to-type`, `varps-to-tm`. A faithful
compatibility shim would have to bundle the new indexed witnesses (`x`, `A`,
`n`, `d : IsDangling …`) and reproduce the old definitional behaviour of the
pasting extension, which contorts the relational core for no benefit on this
pass. Downstream modules should consume `IsPsCtx` / `IsDangling` directly. When
a computed constructor still needs endpoint typing, keep that small bridge local
to the constructor rather than rebuilding a broad computed pasting API.

## Uniqueness and Proof Uniqueness

The relations of this module are *functional* in their numeric/type outputs (a
fixed input determines the result) and *proof-irrelevant* (any two witnesses of
the same statement are equal). The corresponding `*-unique` / `*-uip` proofs —
for dimensions (`hasDimTy-unique`, `hasDimCtx-unique`, `hasDimVar-unique`), the
extension witnesses (`homTypeExt-unique`, `HomTypeExt-uip`, `wkTy²-unique`,
`WkTy²-uip`), and the pasting families (`isPsCtx-dim-unique`,
`isDangling-ty-unique`, `isDangling-dim-unique`, `IsDangling-uip`,
`IsPsCtx-uip`) — now live in `1z-Uniqueness`, alongside the analogous raw-syntax
results from `1a-RawSyntax`.
