# 2d-FunctorialityContextHelpers: Minimal Typed Step Constructors

This file contains only the non-recursive typed helper data used directly by
`2e-FunctorialityContexts`.

There are two branch-local situations:

- the ordinary snoc case, where the newest declaration is kept as a single
  substituted variable
- the split case, where the newest declaration is replaced by source copy,
  target copy, and comparison edge

The public surface is intentionally small:

- `split-step-ctx`
- `split-edge-ty`
- `splitCtx`
- `splitWk³`
- `split-src`
- `split-tgt`
- `snoc-vz-after-wk-typed`
- `snoc-src-after-split-typed`
- `snoc-tgt-after-split-typed`

Everything else in the file is internal proof plumbing supporting those names.

```agda
module 2d-FunctorialityContextHelpers where

open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import 2a-CaTT
import 1a-preCaTT as Pre
```

## Comparison Edge

The split case first duplicates a type once.

Starting from `A' : Ty Γ`, we pass to the doubled context
`Γ , A' , wkTy A'`, whose two newest variables are the source and target copies
of `A'`. The only real purpose of `SplitEdge` is to package the comparison edge
type between those two variables, together with the endpoint typing lemmas
needed to form that hom-type cleanly.

So yes: conceptually, `SplitEdge` is just the local definition of the edge type
once the doubled context has been fixed.

```agda
private
  module SplitEdge {Γ : Ctx} (A' : Ty Γ) where
    firstCopyCtx : Ctx
    firstCopyCtx = Γ , A'

    secondCopyTy : Ty firstCopyCtx
    secondCopyTy = wkTy A'

    doubleCtx : Ctx
    doubleCtx = firstCopyCtx , secondCopyTy

    edgeBase : Ty doubleCtx
    edgeBase = wkTy secondCopyTy

    src : Tm doubleCtx
    src = vs (zero {A = A'})

    tgt : Tm doubleCtx
    tgt = vz

    abstract
      src-typed : TmTyEq {Γ = doubleCtx} src edgeBase
      src-typed =
        trans
          (cong Pre.wkTy (sym (wkTyCommRaw {Γ = Γ} {B = A'} A')))
          (sym
            (wkTyCommRaw
              {Γ = firstCopyCtx}
              {B = secondCopyTy}
              secondCopyTy))

      tgt-typed : TmTyEq {Γ = doubleCtx} tgt edgeBase
      tgt-typed =
        sym
          (wkTyCommRaw
            {Γ = firstCopyCtx}
            {B = secondCopyTy}
            secondCopyTy)

    edge : Ty doubleCtx
    edge = [ edgeBase ] src ⇒ tgt :[ Ty-ext src-typed , Ty-ext tgt-typed ]
```

## Split Branch Package

`SplitBranch` packages the whole split branch used in `2e`.

Given `A : Ty Γ` and `σ : Sub Δ Γ`, it first forms the substituted type
`A [ σ ]T` over `Δ`, then applies `SplitEdge` to create the two endpoint copies
and their comparison edge, and finally extends once more by that edge. This is
the full context used when the newest variable is selected for functoriality.

The conceptual data here are short:

- the split context itself
- the triple weakening back to `Δ`
- the composite substitution back to `Γ`
- the chosen source and target variables in the split context

Most of the length of `SplitBranch` is then one transport proof: it shows that
those source and target variables have type `A` after pulling back along the
composite map back to `Γ`.

```agda
private
  module SplitBranch {Γ Δ : Ctx} (A : Ty Γ) (σ : Sub Δ Γ) where
    substitutedTy : Ty Δ
    substitutedTy = A [ σ ]T

    module Edge = SplitEdge {Γ = Δ} substitutedTy

    splitCtx : Ctx
    splitCtx = Edge.doubleCtx , Edge.edge

    splitWk : Sub splitCtx Δ
    splitWk = wk³

    splitSub : Sub splitCtx Γ
    splitSub = σ ∘ splitWk

    edgeBaseInSplitCtx : Ty splitCtx
    edgeBaseInSplitCtx = wkTy Edge.edgeBase

    src : Tm splitCtx
    src = vs (Pre.vs Pre.vz)

    tgt : Tm splitCtx
    tgt = vs Pre.vz

    abstract
      src-typed : TmTyEq {Γ = splitCtx} src edgeBaseInSplitCtx
      src-typed =
        trans
          (cong Pre.wkTy Edge.src-typed)
          (sym
            (wkTyCommRaw
              {Γ = Edge.doubleCtx}
              {B = Edge.edge}
              Edge.edgeBase))

      tgt-typed : TmTyEq {Γ = splitCtx} tgt edgeBaseInSplitCtx
      tgt-typed =
        trans
          (cong Pre.wkTy Edge.tgt-typed)
          (sym
            (wkTyCommRaw
              {Γ = Edge.doubleCtx}
              {B = Edge.edge}
              Edge.edgeBase))

      rawSubstitutedTy : Pre.Ty (Raw-Ctx Δ)
      rawSubstitutedTy = Raw-Ty substitutedTy

      rawA : Pre.Ty (Raw-Ctx Γ)
      rawA = Raw-Ty A

      rawSecondCopyTy : Pre.Ty (Raw-Ctx (Δ , substitutedTy))
      rawSecondCopyTy = Raw-Ty Edge.secondCopyTy

      rawEdgeBase : Pre.Ty (Raw-Ctx Edge.doubleCtx)
      rawEdgeBase = Raw-Ty Edge.edgeBase

      wkSubstituted : Sub (Δ , substitutedTy) Δ
      wkSubstituted = wk

      wkDouble : Sub Edge.doubleCtx (Δ , substitutedTy)
      wkDouble = wk

      wkEdge : Sub splitCtx Edge.doubleCtx
      wkEdge = wk

      wkTail : Sub splitCtx (Δ , substitutedTy)
      wkTail = wkDouble ∘ wkEdge

      rawWkSubstituted :
        Pre.Sub (Raw-Ctx (Δ , substitutedTy)) (Raw-Ctx Δ)
      rawWkSubstituted = Raw-Sub wkSubstituted

      rawWkDouble :
        Pre.Sub (Raw-Ctx Edge.doubleCtx) (Raw-Ctx (Δ , substitutedTy))
      rawWkDouble = Raw-Sub wkDouble

      rawWkEdge :
        Pre.Sub (Raw-Ctx splitCtx) (Raw-Ctx Edge.doubleCtx)
      rawWkEdge = Raw-Sub wkEdge

      splitWk-raw :
        Raw-Sub splitWk
        ≡ Pre._∘_ rawWkSubstituted (Pre._∘_ rawWkDouble rawWkEdge)
      splitWk-raw = refl

      σSubstituted : Sub (Δ , substitutedTy) Γ
      σSubstituted = σ ∘ wkSubstituted

      σDouble : Sub Edge.doubleCtx Γ
      σDouble = σSubstituted ∘ wkDouble

      σSplit : Sub splitCtx Γ
      σSplit = σDouble ∘ wkEdge

      rawσ : Pre.Sub (Raw-Ctx Δ) (Raw-Ctx Γ)
      rawσ = Raw-Sub σ

      rawσSubstituted :
        Pre.Sub (Raw-Ctx (Δ , substitutedTy)) (Raw-Ctx Γ)
      rawσSubstituted = Raw-Sub σSubstituted

      rawσDouble : Pre.Sub (Raw-Ctx Edge.doubleCtx) (Raw-Ctx Γ)
      rawσDouble = Raw-Sub σDouble

      rawσSplit : Pre.Sub (Raw-Ctx splitCtx) (Raw-Ctx Γ)
      rawσSplit = Raw-Sub σSplit

      -- The remaining lemmas transport the evident endpoint type in the split
      -- context into the substituted type `A [ splitSub ]T`.

      split-triple-wk-step1 :
        Raw-Ty edgeBaseInSplitCtx
        ≡ Pre.wkTy {A = Raw-Ty Edge.edge} rawEdgeBase
      split-triple-wk-step1 = refl

      split-triple-wk-step2 :
        Pre.wkTy {A = Raw-Ty Edge.edge} rawEdgeBase
        ≡ Pre.wkTy
            {A = Raw-Ty Edge.edge}
            (Pre.wkTy {A = Raw-Ty Edge.secondCopyTy} rawSecondCopyTy)
      split-triple-wk-step2 = refl

      split-triple-wk-step3 :
        Pre.wkTy
          {A = Raw-Ty Edge.edge}
          (Pre.wkTy {A = Raw-Ty Edge.secondCopyTy} rawSecondCopyTy)
        ≡ Pre.wkTy
            {A = Raw-Ty Edge.edge}
            (Pre.wkTy
              {A = Raw-Ty Edge.secondCopyTy}
              (Pre.wkTy {A = Raw-Ty substitutedTy} rawSubstitutedTy))
      split-triple-wk-step3 = refl

      split-triple-wk-step4 :
        Pre.wkTy
          {A = Raw-Ty Edge.edge}
          (Pre.wkTy
            {A = Raw-Ty Edge.secondCopyTy}
            (Pre.wkTy {A = Raw-Ty substitutedTy} rawSubstitutedTy))
        ≡ Pre.wkTy
            {A = Raw-Ty Edge.edge}
            (Pre.wkTy
              {A = Raw-Ty Edge.secondCopyTy}
              (Pre.wkTy
                {A = Raw-Ty substitutedTy}
                (Pre._[_]T rawA (Raw-Sub σ))))
      split-triple-wk-step4 =
        cong
          (Pre.wkTy {A = Raw-Ty Edge.edge})
          (cong
            (Pre.wkTy {A = Raw-Ty Edge.secondCopyTy})
            (cong
              (Pre.wkTy {A = Raw-Ty substitutedTy})
              (Raw-Ty-Sub A σ)))

      split-triple-wk-mid :
        Raw-Ty edgeBaseInSplitCtx
        ≡ Pre.wkTy
            {A = Raw-Ty Edge.edge}
            (Pre.wkTy
              {A = Raw-Ty Edge.secondCopyTy}
              (Pre.wkTy
                {A = Raw-Ty substitutedTy}
                (Pre._[_]T rawA (Raw-Sub σ))))
      split-triple-wk-mid =
        trans split-triple-wk-step1
          (trans split-triple-wk-step2
            (trans split-triple-wk-step3 split-triple-wk-step4))

      split-triple-wk-suffix-step1 :
        Pre.wkTy
          {A = Raw-Ty Edge.edge}
          (Pre.wkTy
            {A = Raw-Ty Edge.secondCopyTy}
            (Pre.wkTy
              {A = Raw-Ty substitutedTy}
              (Pre._[_]T rawA rawσ)))
        ≡ Pre.wkTy
            {A = Raw-Ty Edge.edge}
            (Pre.wkTy
              {A = Raw-Ty Edge.secondCopyTy}
              (Pre._[_]T rawA rawσSubstituted))
      split-triple-wk-suffix-step1 =
        cong
          (Pre.wkTy {A = Raw-Ty Edge.edge})
          (cong
            (Pre.wkTy {A = Raw-Ty Edge.secondCopyTy})
            (Pre.push-wk-onto-sub
              {B = Raw-Ty substitutedTy}
              (Raw-Ty A)
              (Raw-Sub σ)))

      split-triple-wk-suffix-step2 :
        Pre.wkTy
          {A = Raw-Ty Edge.edge}
          (Pre.wkTy
            {A = Raw-Ty Edge.secondCopyTy}
            (Pre._[_]T rawA rawσSubstituted))
        ≡ Pre.wkTy
            {A = Raw-Ty Edge.edge}
            (Pre._[_]T rawA rawσDouble)
      split-triple-wk-suffix-step2 =
        cong
          (Pre.wkTy {A = Raw-Ty Edge.edge})
          (Pre.push-wk-onto-sub
            {B = Raw-Ty Edge.secondCopyTy}
            (Raw-Ty A)
            rawσSubstituted)

      split-triple-wk-suffix-step3 :
        Pre.wkTy
          {A = Raw-Ty Edge.edge}
          (Pre._[_]T rawA rawσDouble)
        ≡ Pre._[_]T
            {Γ = Raw-Ctx splitCtx}
            {Δ = Raw-Ctx Γ}
            rawA
            rawσSplit
      split-triple-wk-suffix-step3 =
        Pre.push-wk-onto-sub {B = Raw-Ty Edge.edge} (Raw-Ty A) rawσDouble

      split-triple-wk-suffix :
        Pre._[_]T
          {Γ = Raw-Ctx splitCtx}
          {Δ = Raw-Ctx Γ}
          rawA
          rawσSplit
        ≡ Pre._[_]T
            {Γ = Raw-Ctx splitCtx}
            {Δ = Raw-Ctx Γ}
            rawA
            (Raw-Sub splitSub)
      split-triple-wk-suffix =
        cong
          (Pre._[_]T
            {Γ = Raw-Ctx splitCtx}
            {Δ = Raw-Ctx Γ}
            rawA)
          (trans
            (Raw-Sub-assoc σSubstituted wkDouble wkEdge)
            (trans
              (Raw-Sub-assoc σ wkSubstituted wkTail)
              (cong
                (λ X →
                  Pre._∘_
                    {Γ = Raw-Ctx splitCtx}
                    {Δ = Raw-Ctx Δ}
                    {Θ = Raw-Ctx Γ}
                    rawσ
                    X)
                (sym splitWk-raw))))

      split-triple-wk-typed :
        Raw-Ty edgeBaseInSplitCtx
        ≡ Pre._[_]T
            {Γ = Raw-Ctx splitCtx}
            {Δ = Raw-Ctx Γ}
            rawA
            (Raw-Sub splitSub)
      split-triple-wk-typed =
        trans split-triple-wk-mid
          (trans split-triple-wk-suffix-step1
            (trans split-triple-wk-suffix-step2
              (trans split-triple-wk-suffix-step3
                split-triple-wk-suffix)))

      snoc-tgt-after-split-typed :
        TmTyEqSub
          {Γ = splitCtx}
          {Δ = Γ}
          tgt
          A
          splitSub
      snoc-tgt-after-split-typed =
        trans
          (cong Pre.wkTy Edge.tgt-typed)
          (trans
            (sym split-triple-wk-step1)
            split-triple-wk-typed)

      snoc-src-after-split-typed :
        TmTyEqSub
          {Γ = splitCtx}
          {Δ = Γ}
          src
          A
          splitSub
      snoc-src-after-split-typed =
        trans
          (cong Pre.wkTy Edge.src-typed)
          (trans
            (sym split-triple-wk-step1)
            split-triple-wk-typed)
```

## Public Helpers

The rest of the file simply exposes the pieces of `SplitEdge` and `SplitBranch`
that `2e` actually uses.

```agda
split-step-ctx : ∀ {Δ} (B : Ty Δ) → Ctx
split-step-ctx {Δ} B =
  (SplitEdge.doubleCtx {Γ = Δ} B) , SplitEdge.edge {Γ = Δ} B

split-edge-ty : ∀ {Δ} (B : Ty Δ) → Ty (((Δ , B) , wkTy B))
split-edge-ty {Δ} B = SplitEdge.edge {Γ = Δ} B

splitCtx :
  ∀ {Γ Δ} (A : Ty Γ) (σ : Sub Δ Γ)
  → Ctx
splitCtx {Γ} {Δ} A σ = SplitBranch.splitCtx {Γ = Γ} {Δ = Δ} A σ

splitWk³ :
  ∀ {Γ Δ} (A : Ty Γ) (σ : Sub Δ Γ)
  → Sub (splitCtx A σ) Δ
splitWk³ {Γ} {Δ} A σ = SplitBranch.splitWk {Γ = Γ} {Δ = Δ} A σ

split-src :
  ∀ {Γ Δ} (A : Ty Γ) (σ : Sub Δ Γ)
  → Tm (splitCtx A σ)
split-src {Γ} {Δ} A σ = SplitBranch.src {Γ = Γ} {Δ = Δ} A σ

split-tgt :
  ∀ {Γ Δ} (A : Ty Γ) (σ : Sub Δ Γ)
  → Tm (splitCtx A σ)
split-tgt {Γ} {Δ} A σ = SplitBranch.tgt {Γ = Γ} {Δ = Δ} A σ

abstract
  snoc-src-after-split-typed :
    ∀ {Γ Δ} (A : Ty Γ) (σ : Sub Δ Γ)
    → TmTyEqSub
        {Γ = splitCtx A σ}
        {Δ = Γ}
        (split-src A σ)
        A
        (σ ∘ splitWk³ A σ)
  snoc-src-after-split-typed {Γ} {Δ} A σ =
    SplitBranch.snoc-src-after-split-typed {Γ = Γ} {Δ = Δ} A σ

  snoc-tgt-after-split-typed :
    ∀ {Γ Δ} (A : Ty Γ) (σ : Sub Δ Γ)
    → TmTyEqSub
        {Γ = splitCtx A σ}
        {Δ = Γ}
        (split-tgt A σ)
        A
        (σ ∘ splitWk³ A σ)
  snoc-tgt-after-split-typed {Γ} {Δ} A σ =
    SplitBranch.snoc-tgt-after-split-typed {Γ = Γ} {Δ = Δ} A σ

  snoc-vz-after-wk-typed :
    ∀ {Γ Δ} (A : Ty Γ) (σ : Sub Δ Γ)
    → TmTyEqSub
        {Γ = (Δ , (A [ σ ]T))}
        {Δ = Γ}
        (vz {Γ = Δ} {A = A [ σ ]T})
        A
        (σ ∘ wk)
  snoc-vz-after-wk-typed {Γ} {Δ} A σ =
    trans
      (cong Pre.wkTy (Raw-Ty-Sub A σ))
      (trans
        (sym
          (Pre.wkTy-[]T
            (Raw-Ty A)
            (Raw-Sub σ)))
        (cong
          (Pre._[_]T (Raw-Ty A))
          (sym
            (Pre.∘wk
              {A = Raw-Ty (A [ σ ]T)}
              (Raw-Sub σ)))))
```
