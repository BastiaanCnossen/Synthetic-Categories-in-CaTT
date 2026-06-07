# 2g-Functoriality: Depth-0 Functoriality Construction

This file now records the actual recursive shape of the depth-0 functoriality
construction.

The definitions of term and substitution functoriality are present; what
remains postulated are the genuinely hard side conditions:

- substitution preserves computed types
- coherence functoriality
- inverse-image preservation of local maximality
- the branch-local typing facts for recursive substitutions
- the final typing theorem for functorialized terms

```agda
module 2g-Functoriality where

open import Agda.Builtin.Equality
open import Data.Bool.Base using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import 1a-preCaTT as Pre
open import 2b-Wrappers
open import 2d-FunctorialityContextHelpers using (split-edge-ty)
open import 2e-FunctorialityContexts
open import 2f-Depth public
```

## Functoriality Interfaces

```agda
infixl 8 _↑var_ _↑ty_ _↑tm_ _↑sub_
```

## Easy Raw-First Lifts

```agda
postulate
  tyOfSub :
    {Γ Δ : Ctx}
    {t : Tm Δ}
    {A : Ty Δ}
    {σ : Sub Γ Δ}
    → tyOf {Γ = Δ} t ≡ A
    → tyOf {Γ = Γ} (_[_]t {Γ = Γ} {Δ = Δ} t σ) ≡ _[_]T {Γ = Γ} {Δ = Δ} A σ

tyOf≡→TmTyEq :
  {Γ : Ctx}
  {t : Tm Γ}
  {A : Ty Γ}
  → tyOf {Γ = Γ} t ≡ A
  → TmTyEq {Γ = Γ} t A
tyOf≡→TmTyEq p = cong Raw-Ty p
```

## Variables and Types

```agda
mutual
  ↑var-empty : (X : Var ∅ → Bool) → (x : Var ∅) → Tm (_↑_ ∅ X)
  ↑var-empty X ()

  ↑var-snoc :
    ∀ {Γ} (A : Ty Γ)
    → (x : Var (Γ , A))
    → (X : Var (Γ , A) → Bool)
    → Tm (_↑_ (Γ , A) X)
  ↑var-snoc {Γ} A Pre.vz X with X Pre.vz
  ... | false = var Pre.vz
  ... | true = var Pre.vz
  ↑var-snoc {Γ} A (Pre.vs y) X with X Pre.vz
  ... | false = (_↑var_ {Γ = Γ} y (dropLast {Γ = Γ} {A = A} X)) [ wk ]t
  ... | true = (_↑var_ {Γ = Γ} y (dropLast {Γ = Γ} {A = A} X)) [ wk³ ]t

  _↑var_ :
    {Γ : Ctx}
    → (x : Var Γ)
    → (X : Var Γ → Bool)
    → Tm (_↑_ Γ X)
  _↑var_ {Γ} x X with ctx-view Γ
  ... | ∅-view = ↑var-empty X x
  ... | snoc-view {Γ = Γ'} A = ↑var-snoc {Γ = Γ'} A x X

_↑ty_ :
  {Γ : Ctx}
  → (A : Ty Γ)
  → (X : Var Γ → Bool)
  → (lm : all-local-max {Γ = Γ} X ≡ true)
  → depth≤0-ty {Γ = Γ} X A ≡ true
  → (v⁻ : Tm (_↑_ Γ X))
  → (v⁺ : Tm (_↑_ Γ X))
  → TmTyEq {Γ = _↑_ Γ X} v⁻ (_[_]T {Γ = _↑_ Γ X} {Δ = Γ} A (in⁻ Γ X))
  → TmTyEq {Γ = _↑_ Γ X} v⁺ (_[_]T {Γ = _↑_ Γ X} {Δ = Γ} A (in⁺ Γ X lm))
  → Ty (_↑_ Γ X)

_↑ty_ {Γ} A X lm d≤0A v⁻ v⁺ pv⁻ pv⁺ =
  [ A [ in⁻ Γ X ]T ] v⁻ ⇒ v⁺ :[
    TmTyEq→tyOf≡
      {Γ = _↑_ Γ X}
      {t = v⁻}
      {A = A [ in⁻ Γ X ]T}
      pv⁻
  , trans
      (TmTyEq→tyOf≡
        {Γ = _↑_ Γ X}
        {t = v⁺}
        {A = A [ in⁺ Γ X lm ]T}
        pv⁺)
      (sym
        (agree-ty Γ X lm A
          (depth≤0-ty→depends-on-X-ty-false X A d≤0A)))
  ]

```

## Terms and Substitutions

```agda
postulate
  ↑coh :
    {Γ Δ : Ctx}
    → (Γps : CtxPs Δ)
    → (A : Ty Δ)
    → (u v : Tm Δ)
    → (p : TmTyEq u A)
    → (q : TmTyEq v A)
    → (pf : is-full Γps u v ≡ true)
    → (σ : Sub Γ Δ)
    → (X : Var Γ → Bool)
    → (lm : all-local-max {Γ = Γ} X ≡ true)
    → depth=0-tm {Γ = Γ} X (coh Γps A u v p q pf σ) ≡ true
    → Tm (_↑_ Γ X)

  upTm-coh :
    {Γ : Ctx}
    → (t : Tm Γ)
    → (X : Var Γ → Bool)
    → (lm : all-local-max {Γ = Γ} X ≡ true)
    → depth=0-tm {Γ = Γ} X t ≡ true
    → Tm (_↑_ Γ X)

  depth≤0-sub-head-selected→depth=0-tm :
    {Γ Δ : Ctx}
    {A : Ty Δ}
    {γ : Sub Γ Δ}
    {t : Tm Γ}
    {p : TmTyEqSub t A γ}
    → (X : Var Γ → Bool)
    → depends-on-X-tm {Γ = Γ} X t ≡ true
    → depth≤0-sub {Γ = Γ} {Δ = Δ , A} X (⟨ γ , t ⟩∶[ p ]) ≡ true
    → depth=0-tm {Γ = Γ} X t ≡ true

  inv-img-local-max :
    {Γ Δ : Ctx}
    → (σ : Sub Γ Δ)
    → (X : Var Γ → Bool)
    → (lmX : all-local-max {Γ = Γ} X ≡ true)
    → depth≤0-sub {Γ = Γ} {Δ = Δ} X σ ≡ true
    → all-local-max {Γ = Δ} (inv-img {Γ = Γ} {Δ = Δ} σ X) ≡ true

  ↑sub-unsplit-typed :
    {Γ Δ : Ctx}
    {A : Ty Δ}
    {γ : Sub Γ Δ}
    {t : Tm Γ}
    {p : TmTyEqSub t A γ}
    → (X : Var Γ → Bool)
    → (lmX : all-local-max {Γ = Γ} X ≡ true)
    → (lmInvγ : all-local-max {Γ = Δ} (inv-img {Γ = Γ} {Δ = Δ} γ X) ≡ true)
    → (dγ : depth≤0-sub {Γ = Γ} {Δ = Δ} X γ ≡ true)
    → (γ↑ : Sub (_↑_ Γ X) (_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)))
    → depends-on-X-tm {Γ = Γ} X t ≡ false
    → TmTyEqSub
        {Γ = _↑_ Γ X}
        {Δ = _↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)}
        (_[_]t {Γ = _↑_ Γ X} {Δ = Γ} t (in⁻ Γ X))
        (_[_]T
          {Γ = _↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)}
          {Δ = Δ}
          A
          (in⁻ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)))
        γ↑

  ↑sub-split-src-typed :
    {Γ Δ : Ctx}
    {A : Ty Δ}
    {γ : Sub Γ Δ}
    {t : Tm Γ}
    {p : TmTyEqSub t A γ}
    → (X : Var Γ → Bool)
    → (lmX : all-local-max {Γ = Γ} X ≡ true)
    → (lmInvγ : all-local-max {Γ = Δ} (inv-img {Γ = Γ} {Δ = Δ} γ X) ≡ true)
    → (dγ : depth≤0-sub {Γ = Γ} {Δ = Δ} X γ ≡ true)
    → (γ↑ : Sub (_↑_ Γ X) (_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)))
    → depends-on-X-tm {Γ = Γ} X t ≡ true
    → TmTyEqSub
        {Γ = _↑_ Γ X}
        {Δ = _↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)}
        (_[_]t {Γ = _↑_ Γ X} {Δ = Γ} t (in⁻ Γ X))
        (_[_]T
          {Γ = _↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)}
          {Δ = Δ}
          A
          (in⁻ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)))
        γ↑

  ↑sub-split-tgt-typed :
    {Γ Δ : Ctx}
    {A : Ty Δ}
    {γ : Sub Γ Δ}
    {t : Tm Γ}
    {p : TmTyEqSub t A γ}
    → (X : Var Γ → Bool)
    → (lmX : all-local-max {Γ = Γ} X ≡ true)
    → (lmInvγ : all-local-max {Γ = Δ} (inv-img {Γ = Γ} {Δ = Δ} γ X) ≡ true)
    → (dγ : depth≤0-sub {Γ = Γ} {Δ = Δ} X γ ≡ true)
    → (γ↑ : Sub (_↑_ Γ X) (_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)))
    → (σsrc : Sub
        (_↑_ Γ X)
        ((_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))
          , (_[_]T
              {Γ = _↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)}
              {Δ = Δ}
              A
              (in⁻ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)))))
    → depends-on-X-tm {Γ = Γ} X t ≡ true
    → TmTyEqSub
        {Γ = _↑_ Γ X}
        {Δ = ((_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))
          , (_[_]T
              {Γ = _↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)}
              {Δ = Δ}
              A
              (in⁻ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))))}
        (_[_]t {Γ = _↑_ Γ X} {Δ = Γ} t (in⁺ Γ X lmX))
        (wkTy
          (_[_]T
            {Γ = _↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)}
            {Δ = Δ}
            A
            (in⁻ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))))
        σsrc

  ↑sub-split-bridge-typed :
    {Γ Δ : Ctx}
    {A : Ty Δ}
    {γ : Sub Γ Δ}
    {t : Tm Γ}
    {p : TmTyEqSub t A γ}
    → (X : Var Γ → Bool)
    → (lmX : all-local-max {Γ = Γ} X ≡ true)
    → (lmInvγ : all-local-max {Γ = Δ} (inv-img {Γ = Γ} {Δ = Δ} γ X) ≡ true)
    → (dγ : depth≤0-sub {Γ = Γ} {Δ = Δ} X γ ≡ true)
    → (γ↑ : Sub (_↑_ Γ X) (_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)))
    → (σsrc : Sub
        (_↑_ Γ X)
        ((_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))
          , (_[_]T
              {Γ = _↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)}
              {Δ = Δ}
              A
              (in⁻ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)))))
    → (σtgt : Sub
        (_↑_ Γ X)
        (((_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))
            , (_[_]T
                {Γ = _↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)}
                {Δ = Δ}
                A
                (in⁻ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))))
          , wkTy
              (_[_]T
                {Γ = _↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)}
                {Δ = Δ}
                A
                (in⁻ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)))))
    → (t↑ : Tm (_↑_ Γ X))
    → (d0t : depth=0-tm {Γ = Γ} X t ≡ true)
    → depends-on-X-tm {Γ = Γ} X t ≡ true
    → TmTyEqSub
        {Γ = _↑_ Γ X}
        {Δ = (((_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))
            , (_[_]T
                {Γ = _↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)}
                {Δ = Δ}
                A
                (in⁻ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))))
          , wkTy
              (_[_]T
                {Γ = _↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)}
                {Δ = Δ}
                A
                (in⁻ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))))}
        t↑
        (split-edge-ty
          (_[_]T
            {Γ = _↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X)}
            {Δ = Δ}
            A
            (in⁻ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))))
        σtgt
```

```agda
{-# TERMINATING #-}
mutual
  upTm :
    {Γ : Ctx}
    → (t : Tm Γ)
    → (X : Var Γ → Bool)
    → (lm : all-local-max {Γ = Γ} X ≡ true)
    → depth=0-tm {Γ = Γ} X t ≡ true
    → Tm (_↑_ Γ X)

  upSub :
    {Γ Δ : Ctx}
    → (σ : Sub Γ Δ)
    → (X : Var Γ → Bool)
    → (lmX : all-local-max {Γ = Γ} X ≡ true)
    → (lmInv : all-local-max {Γ = Δ} (inv-img {Γ = Γ} {Δ = Δ} σ X) ≡ true)
    → depth≤0-sub {Γ = Γ} {Δ = Δ} X σ ≡ true
    → Sub (_↑_ Γ X) (_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} σ X))

  upTm {Γ = Γ} (mkTm (Pre.var x) (var-wf .x)) X lm d0t =
    _↑var_ {Γ = Γ} x X
  upTm
    {Γ = Γ}
    t@(mkTm (Pre.coh-raw A u v σRaw)
      (coh-wf {Δ = Δ} Γps (mkTy .A Awf) (mkTm .u uwf) (mkTm .v vwf) p q pf (mkSub .σRaw σwf)))
    X lm d0t =
    upTm-coh t X lm d0t

  upSub {Γ = Γ} {Δ = Δ} (mkSub Pre.∅S ∅Swf) X lmX lmInv dσ with ctx-view Δ
  ... | ∅-view = ∅S
  upSub {Γ = Γ} {Δ = Δt}
    (mkSub (Pre.⟨ γRaw , tRaw ⟩)
      (⟨_,_⟩:[_]wf (mkSub .γRaw γwf) (mkTm .tRaw twf) p))
    X lmX lmInv dσ with ctx-view Δt
  ... | snoc-view {Γ = Δ} A with depends-on-X-tm {Γ = Γ} X (mkTm tRaw twf) in depT
  ...   | false =
    ⟨ γ↑ , t [ in⁻ Γ X ]t ⟩∶[
      ↑sub-unsplit-typed
        {A = A} {γ = γ} {t = t} {p = p}
        X lmX lmInvγ dγ γ↑ depT
    ]
    where
      γ : Sub Γ Δ
      γ = mkSub γRaw γwf

      t : Tm Γ
      t = mkTm tRaw twf

      dγ : depth≤0-sub {Γ = Γ} {Δ = Δ} X γ ≡ true
      dγ = depth≤0-sub-tail-local {A = A} {γ = γ} {t = t} {p = p} X dσ

      lmInvγ : all-local-max {Γ = Δ} (inv-img {Γ = Γ} {Δ = Δ} γ X) ≡ true
      lmInvγ = inv-img-local-max γ X lmX dγ

      γ↑ : Sub (_↑_ Γ X) (_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))
      γ↑ = upSub γ X lmX lmInvγ dγ

  ...   | true =
    ⟨ σtgt , t↑ ⟩∶[
      ↑sub-split-bridge-typed
        {A = A} {γ = γ} {t = t} {p = p}
        X lmX lmInvγ dγ γ↑ σsrc σtgt t↑ d0t-head depT
    ]
    where
      γ : Sub Γ Δ
      γ = mkSub γRaw γwf

      t : Tm Γ
      t = mkTm tRaw twf

      dγ : depth≤0-sub {Γ = Γ} {Δ = Δ} X γ ≡ true
      dγ = depth≤0-sub-tail-local {A = A} {γ = γ} {t = t} {p = p} X dσ

      lmInvγ : all-local-max {Γ = Δ} (inv-img {Γ = Γ} {Δ = Δ} γ X) ≡ true
      lmInvγ = inv-img-local-max γ X lmX dγ

      d0t-head : depth=0-tm {Γ = Γ} X t ≡ true
      d0t-head =
        depth≤0-sub-head-selected→depth=0-tm
          {A = A} {γ = γ} {t = t} {p = p}
          X depT dσ

      t↑ : Tm (_↑_ Γ X)
      t↑ = upTm t X lmX d0t-head

      γ↑ : Sub (_↑_ Γ X) (_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))
      γ↑ = upSub γ X lmX lmInvγ dγ

      σsrc :
        Sub
          (_↑_ Γ X)
          ((_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))
            , (A [ in⁻ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X) ]T))
      σsrc =
        ⟨ γ↑ , t [ in⁻ Γ X ]t ⟩∶[
          ↑sub-split-src-typed
            {A = A} {γ = γ} {t = t} {p = p}
            X lmX lmInvγ dγ γ↑ depT
        ]

      σtgt :
        Sub
          (_↑_ Γ X)
          (((_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X))
              , (A [ in⁻ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X) ]T))
            , wkTy (A [ in⁻ Δ (inv-img {Γ = Γ} {Δ = Δ} γ X) ]T))
      σtgt =
        ⟨ σsrc , t [ in⁺ Γ X lmX ]t ⟩∶[
          ↑sub-split-tgt-typed
            {A = A} {γ = γ} {t = t} {p = p}
            X lmX lmInvγ dγ γ↑ σsrc depT
        ]

_↑tm_ :
  {Γ : Ctx}
  → (t : Tm Γ)
  → (X : Var Γ → Bool)
  → (lm : all-local-max {Γ = Γ} X ≡ true)
  → depth=0-tm {Γ = Γ} X t ≡ true
  → Tm (_↑_ Γ X)
_↑tm_ t X = upTm t X

_↑sub_ :
  {Γ Δ : Ctx}
  → (σ : Sub Γ Δ)
  → (X : Var Γ → Bool)
  → (lmX : all-local-max {Γ = Γ} X ≡ true)
  → (lmInv : all-local-max {Γ = Δ} (inv-img {Γ = Γ} {Δ = Δ} σ X) ≡ true)
  → depth≤0-sub {Γ = Γ} {Δ = Δ} X σ ≡ true
  → Sub (_↑_ Γ X) (_↑_ Δ (inv-img {Γ = Γ} {Δ = Δ} σ X))
_↑sub_ σ X = upSub σ X
```

## Deferred Typing Target

```agda
postulate
  ↑tm-TmTyEq :
    {Γ : Ctx}
    → (t : Tm Γ)
    → (A : Ty Γ)
    → (pt : TmTyEq {Γ = Γ} t A)
    → (X : Var Γ → Bool)
    → (lm : all-local-max {Γ = Γ} X ≡ true)
    → (d0t : depth=0-tm {Γ = Γ} X t ≡ true)
    → (d0A : depth≤0-ty {Γ = Γ} X A ≡ true)
    → (p⁻ : TmTyEq
        {Γ = _↑_ Γ X}
        (_[_]t {Γ = _↑_ Γ X} {Δ = Γ} t (in⁻ Γ X))
        (_[_]T {Γ = _↑_ Γ X} {Δ = Γ} A (in⁻ Γ X)))
    → (p⁺ : TmTyEq
        {Γ = _↑_ Γ X}
        (_[_]t {Γ = _↑_ Γ X} {Δ = Γ} t (in⁺ Γ X lm))
        (_[_]T {Γ = _↑_ Γ X} {Δ = Γ} A (in⁺ Γ X lm)))
    → TmTyEq
        {Γ = _↑_ Γ X}
        (_↑tm_ t X lm d0t)
        (_↑ty_ A X lm d0A
          (_[_]t {Γ = _↑_ Γ X} {Δ = Γ} t (in⁻ Γ X))
          (_[_]t {Γ = _↑_ Γ X} {Δ = Γ} t (in⁺ Γ X lm))
          p⁻
          p⁺)
```
