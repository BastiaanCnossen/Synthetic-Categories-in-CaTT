# 4c-LaxAlgebra: Lax Algebra Operations On Diagram Homs

This file records the term-level operations on the chosen diagram-hom carrier.
The specification of diagram homs lives in `4b-DiagramHoms`; the chosen carrier
`dhom` is supplied by `4b-DiagramHoms-Comp`.

The operations split into two clearly different kinds, and the file is organized
around that distinction:

- **Genuine algebraic operations** on diagram homs, whose construction is *not yet
  understood*. These are real categorical structure — composition and inversion of
  lax transformations between diagram morphisms — not substitution bookkeeping:
      `dhom-comp : DTm (dhom d₂ d₃) → DTm (dhom d₁ d₂) → DTm (dhom d₁ d₃)`
      `dhom-inv  : DTm (dhom d₁ d₂) → DTm (dhom d₂ d₁)`
  They stay postulated because we do not yet know how to build them from the
  relational naturality data.

- **Structural / functorial bookkeeping**, which is *expected to be definable* once
  the hom/naturality comparison infrastructure is complete:
      `dhom-subst`   — reindexing a diagram hom along a context substitution `σ`;
      `dhom-rwhisk`  — (provisional, currently unused) right whiskering by two
                       substitutions `σ₁ , σ₂`.
  These remain postulated for now, but the prerequisites are in place: the comparison
  substitution (`dhom-over-sub` / `dhom-over-sub-ext` in `4b-DiagramHoms-Comp`) is fully
  constructed, and the substitution-naturality of the naturality type (`↑ty-[]T` in
  `3b-Naturality-Comp`) is now postulated. What remains for `dhom-subst` is mechanical:
  the hom-type commutation and a computed diagram-term substitution (see below).

- **Entry maps**, which *are* defined here as plain structural recursions now that
  `4a-Diagrams` provides `Entry`:
      `dhom-over-entry` / `dhom-over-entry-inv` (relative, primary), and the derived
      `dhom-entry` / `dhom-entry-inv` for ordinary diagram terms.

```agda
module 4c-LaxAlgebra where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import 2a-CaTT
open import 4a-Diagrams
open import 4b-DiagramHoms using (toOver)
open import 4b-DiagramHoms-Comp
```

## Composition and inverse

`dhom-comp` composes two diagram-hom terms; `dhom-inv` inverts one. At present, we
do not yet know how to mathematically define these.

```agda
postulate
  dhom-comp :
    {Γ : Ctx} {D : DTy Γ} →
    {d₁ d₂ d₃ : DTm D} →
    DTm (dhom d₂ d₃) →
    DTm (dhom d₁ d₂) →
    DTm (dhom d₁ d₃)

  dhom-inv :
    {Γ : Ctx} {D : DTy Γ} →
    {d₁ d₂ : DTm D} →
    DTm (dhom d₁ d₂) →
    DTm (dhom d₂ d₁)
```

## Substitution of a diagram hom

`dhom-subst` reindexes a diagram-hom term along a context substitution `σ : Δ → Γ`.

**Status of the reduction.** The genuine naturality input is now available: the
substitution-naturality of the naturality type, `↑ty-[]T` (with `↑sub-ext`), is
postulated in `3b-Naturality-Comp`. With it, `dhom-subst` reduces to two *mechanical*
(naturality-free) pieces that are not yet built:

1. the **hom-type commutation** `SubstDTy σ (dhom d₁ d₂) (dhom d₁′ d₂′) ρ`, by recursion
   on the two sections — each new component `↑ty (dty-sel E₀) A [ dhom-over-sub-ext … ]T`
   commutes by `↑ty-[]T` together with the (now-built) comparison substitution; and
2. a **computed realizer for substituting a diagram term** along `σ`
   (`SubstDTm σ sD d d′ → DTm D′`), i.e. the `DTm`-level analogue of `dtm-sub` /
   `dover-sub` — pure substitution algebra, no naturality.

Given (1) and (2), `dhom-subst t = realize (homCommutation) t`. Until the realizer and
the commutation witness are built, it stays a postulate.

```agda
postulate
  dhom-subst :
    {Γ Δ : Ctx} →
    {σ : Sub Δ Γ} →
    {D : DTy Γ} {D′ : DTy Δ} →
    {ρ : Sub (Δ ▸▸ D′) (Γ ▸▸ D)} →
    (sD : SubstDTy σ D D′ ρ) →
    {d₁ d₂ : DTm D} →
    {d₁′ d₂′ : DTm D′} →
    SubstDTm σ sD d₁ d₁′ →
    SubstDTm σ sD d₂ d₂′ →
    DTm (dhom d₁ d₂) →
    DTm (dhom d₁′ d₂′)
```

## Right whiskering

> **⚠️ Provisional signature, currently unused.** A search of the live (non-archive)
> files shows `dhom-rwhisk` is not referenced anywhere outside this module. The type
> below is almost certainly too strong (see "Looseness to tighten later"): it relates two
> substitution instances of `d` along *arbitrary, unconnected* substitutions `σ₁ , σ₂`,
> with no witness that the two are joined by a morphism. The fix is to carry such a
> comparison/hom witness relating `σ₁` and `σ₂` and produce the hom from it. Since nothing
> downstream depends on the current shape, we leave the postulate in place but flag it as
> provisional; do **not** build on it without first tightening the signature.

`dhom-rwhisk` whiskers a single diagram term `d : DTm A` by two substitutions
`σ₁ , σ₂ : Δ → Γ`, producing the diagram hom between the two substitution-instances of
`d`. The substituted diagram `B` and the two instances `d₁ , d₂ : DTm B` are given as
**explicit** outputs, recognized by the relation-first `SubstDTy` / `SubstDTm` families
from `4a-Diagrams` (replacing the computed `d [ σᵢ ]dt`).

```agda
postulate
  dhom-rwhisk :
    {Γ Δ : Ctx} →
    {A : DTy Γ} {B : DTy Δ} →
    (d : DTm A) →
    (σ₁ σ₂ : Sub Δ Γ) →
    {ρ₁ ρ₂ : Sub (Δ ▸▸ B) (Γ ▸▸ A)} →
    (s₁ : SubstDTy σ₁ A B ρ₁) →
    (s₂ : SubstDTy σ₂ A B ρ₂) →
    {d₁ d₂ : DTm B} →
    SubstDTm σ₁ s₁ d d₁ →
    SubstDTm σ₂ s₂ d d₂ →
    DTm (dhom d₁ d₂)
```

**Looseness to tighten later.** The type does not enforce that the two substitutions
`σ₁ , σ₂` are *connected by a morphism* (in the intended use they are the negative and
positive endpoint substitutions induced by a source hom, which is exactly what makes
`d₁ → d₂` a hom). With arbitrary unrelated `σ₁ , σ₂` the postulate would assert a hom
that need not exist. To tighten it, one would carry evidence relating `σ₁` and `σ₂` (an
endpoint/`NatIn⁻`/`NatIn⁺`-style witness) and have the construction produce the hom from
that. For now we keep the postulate as is and document the gap rather than
over-specifying it.

## Entry maps

An easy recursion shows that the entries of a diagram hom of `D` agree with those of `D`.

```agda
dhom-over-entry :
  {Γ : Ctx} {D E : DTy Γ} →
  (d₁ d₂ : DTmOverDTy D E) →
  Entry E →
  Entry (dhom-over d₁ d₂)
dhom-over-entry ◆ᴰ ◆ᴰ ()
dhom-over-entry (d₁ ▸ᴰ _ [ _ ][ _ ]) (d₂ ▸ᴰ _ [ _ ][ _ ]) here      = here
dhom-over-entry (d₁ ▸ᴰ _ [ _ ][ _ ]) (d₂ ▸ᴰ _ [ _ ][ _ ]) (there e) =
  there (dhom-over-entry d₁ d₂ e)

dhom-over-entry-inv :
  {Γ : Ctx} {D E : DTy Γ} →
  (d₁ d₂ : DTmOverDTy D E) →
  Entry (dhom-over d₁ d₂) →
  Entry E
dhom-over-entry-inv ◆ᴰ ◆ᴰ ()
dhom-over-entry-inv (d₁ ▸ᴰ _ [ _ ][ _ ]) (d₂ ▸ᴰ _ [ _ ][ _ ]) here      = here
dhom-over-entry-inv (d₁ ▸ᴰ _ [ _ ][ _ ]) (d₂ ▸ᴰ _ [ _ ][ _ ]) (there e) =
  there (dhom-over-entry-inv d₁ d₂ e)
```

The following is the specialization to plain diagram terms:

```agda
dhom-entry :
  {Γ : Ctx} {D : DTy Γ} →
  (d₁ d₂ : DTm D) →
  Entry D →
  Entry (dhom d₁ d₂)
dhom-entry d₁ d₂ e = dhom-over-entry (toOver d₁) (toOver d₂) e

dhom-entry-inv :
  {Γ : Ctx} {D : DTy Γ} →
  (d₁ d₂ : DTm D) →
  Entry (dhom d₁ d₂) →
  Entry D
dhom-entry-inv d₁ d₂ e = dhom-over-entry-inv (toOver d₁) (toOver d₂) e
```

The two position maps are mutually inverse, by the same structural recursion. (These
laws are convenient but not load-bearing; they are kept because Agda accepts them
directly.)

```agda
dhom-over-entry-inv-entry :
  {Γ : Ctx} {D E : DTy Γ} →
  (d₁ d₂ : DTmOverDTy D E) →
  (e : Entry E) →
  dhom-over-entry-inv d₁ d₂ (dhom-over-entry d₁ d₂ e) ≡ e
dhom-over-entry-inv-entry ◆ᴰ ◆ᴰ ()
dhom-over-entry-inv-entry (d₁ ▸ᴰ _ [ _ ][ _ ]) (d₂ ▸ᴰ _ [ _ ][ _ ]) here      = refl
dhom-over-entry-inv-entry (d₁ ▸ᴰ _ [ _ ][ _ ]) (d₂ ▸ᴰ _ [ _ ][ _ ]) (there e) =
  cong there (dhom-over-entry-inv-entry d₁ d₂ e)

dhom-over-entry-entry-inv :
  {Γ : Ctx} {D E : DTy Γ} →
  (d₁ d₂ : DTmOverDTy D E) →
  (e : Entry (dhom-over d₁ d₂)) →
  dhom-over-entry d₁ d₂ (dhom-over-entry-inv d₁ d₂ e) ≡ e
dhom-over-entry-entry-inv ◆ᴰ ◆ᴰ ()
dhom-over-entry-entry-inv (d₁ ▸ᴰ _ [ _ ][ _ ]) (d₂ ▸ᴰ _ [ _ ][ _ ]) here      = refl
dhom-over-entry-entry-inv (d₁ ▸ᴰ _ [ _ ][ _ ]) (d₂ ▸ᴰ _ [ _ ][ _ ]) (there e) =
  cong there (dhom-over-entry-entry-inv d₁ d₂ e)
```

## Status

The file now mixes three kinds of declaration:

- **Open mathematics (postulated):** `dhom-comp`, `dhom-inv` — genuine vertical
  composition and inversion of lax transformations, whose construction from the
  relational naturality data is not yet understood.
- **Deferred bookkeeping (postulated):** `dhom-subst` and the provisional `dhom-rwhisk`
  — structural/functorial reindexing, still to be wired up. The comparison substitution
  they build on (`dhom-over-sub` / `dhom-over-sub-ext` in `4b-DiagramHoms-Comp`) is now
  fully constructed.
- **Defined now:** the entry maps `dhom-over-entry`, `dhom-over-entry-inv` and their
  derived ordinary forms `dhom-entry`, `dhom-entry-inv`, plus the inverse laws.

These give the later diagram-morphism files (`4d`–`4h`, `5b`) the term-level API they
expect while the relational specification continues to live in `DHom`
(`4b-DiagramHoms`).
