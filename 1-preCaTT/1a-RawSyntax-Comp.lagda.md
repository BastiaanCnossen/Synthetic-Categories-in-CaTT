# 1a-RawSyntax-Comp: Computed Raw Operations

This module isolates the structurally recursive raw operations and their
equational theory. The proposition-facing raw syntax and relations live in
`1a-RawSyntax`; import this module only when a construction genuinely needs a
computed output or a compatibility bridge.

```agda
module 1a-RawSyntax-Comp where

open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)
open import 1a-RawSyntax public
-- Uniqueness lemmas used by the `*-rel→≡` bridges below now live in
-- `1z-Uniqueness`.
open import 1z-Uniqueness using (wkTy-unique; wkTm-unique)

infixl 8 _[_]T _[_]t
infixr 10 _∘_
```

## Weakening and Identity Substitution

Weakening shifts all terms, types, and substitutions across a new variable
binder. It is defined by mutual structural recursion: `wkTy` and `wkTm` call
each other, and both call `wkSub`.

```agda
mutual
  -- Weaken a type across a new binder A.
  wkTy : {Γ : RawCtx} {A : RawTy Γ} → RawTy Γ → RawTy (Γ ▸ A)
  wkTy ⋆ = ⋆
  wkTy ([ A ] t ⇒ u) = [ wkTy A ] wkTm t ⇒ wkTm u

  -- Weaken a term across a new binder. Variables are shifted; coherences have
  -- their stored substitution weakened.
  wkTm : {Γ : RawCtx} {A : RawTy Γ} → RawTm Γ → RawTm (Γ ▸ A)
  wkTm (var x) = var (succ x)
  wkTm (coh A u v σ) = coh A u v (wkSub σ)

  -- Weaken each term in a substitution.
  wkSub : {Γ Δ : RawCtx} {A : RawTy Γ} → RawSub Γ Δ → RawSub (Γ ▸ A) Δ
  wkSub ◆S = ◆S
  wkSub ⟨ σ , t ⟩ = ⟨ wkSub σ , wkTm t ⟩

mutual
  wkTy-rel : ∀ {Γ : RawCtx} {A : RawTy Γ} (B : RawTy Γ)
    → WkTy {A = A} B (wkTy {A = A} B)
  wkTy-rel ⋆ = wk-⋆
  wkTy-rel ([ B ] t ⇒ u) = wk-hom (wkTy-rel B) (wkTm-rel t) (wkTm-rel u)

  wkTm-rel : ∀ {Γ : RawCtx} {A : RawTy Γ} (t : RawTm Γ)
    → WkTm {A = A} t (wkTm {A = A} t)
  wkTm-rel (var x) = wk-var
  wkTm-rel (coh B u v σ) = wk-coh (wkSub-rel σ)

  wkSub-rel : ∀ {Γ Δ : RawCtx} {A : RawTy Γ} (σ : RawSub Γ Δ)
    → WkSub {A = A} σ (wkSub {A = A} σ)
  wkSub-rel ◆S = wk-empty
  wkSub-rel ⟨ σ , t ⟩ = wk-snoc (wkSub-rel σ) (wkTm-rel t)

wkTy-rel→≡ : ∀ {Γ : RawCtx} {A B : RawTy Γ} {B' : RawTy (Γ ▸ A)}
  → WkTy {A = A} B B' → wkTy {A = A} B ≡ B'
wkTy-rel→≡ {B = B} p = wkTy-unique (wkTy-rel B) p

wkTm-rel→≡ : ∀ {Γ : RawCtx} {A : RawTy Γ} {t : RawTm Γ} {t' : RawTm (Γ ▸ A)}
  → WkTm {A = A} t t' → wkTm {A = A} t ≡ t'
wkTm-rel→≡ {t = t} p = wkTm-unique (wkTm-rel t) p

-- The identity substitution maps each variable to itself.
-- It is built by recursion: the empty context maps to ◆S, and a snoc-context
-- maps to ⟨ wkSub (idS Γ) , var zero ⟩.
idS : (Γ : RawCtx) → RawSub Γ Γ
idS ◆ = ◆S
idS (Γ ▸ A) = ⟨ wkSub (idS Γ) , var zero ⟩
```

### Weakening preservation for the substitution relations

The relational substitution evaluators are preserved by weakening the
substitution: weakening `σ` weakens the recorded output. These are mutually
recursive and structural, matching `wkSub`/`wkTy`/`wkTm`.

```agda
mutual
  substVar-wkSub : ∀ {Γ Δ : RawCtx} {A : RawTy Γ} {x : RawVar Δ} {σ : RawSub Γ Δ} {t : RawTm Γ}
    → SubstVar x σ t
    → SubstVar x (wkSub {A = A} σ) (wkTm {A = A} t)
  substVar-wkSub sub-zero = sub-zero
  substVar-wkSub (sub-succ p) = sub-succ (substVar-wkSub p)

  substTy-wkSub : ∀ {Γ Δ : RawCtx} {A : RawTy Γ} {B : RawTy Δ} {σ : RawSub Γ Δ} {C : RawTy Γ}
    → SubstTy B σ C
    → SubstTy B (wkSub {A = A} σ) (wkTy {A = A} C)
  substTy-wkSub sub-⋆ = sub-⋆
  substTy-wkSub (sub-hom pB pt pu) =
    sub-hom (substTy-wkSub pB) (substTm-wkSub pt) (substTm-wkSub pu)

  substTm-wkSub : ∀ {Γ Δ : RawCtx} {A : RawTy Γ} {t : RawTm Δ} {σ : RawSub Γ Δ} {u : RawTm Γ}
    → SubstTm t σ u
    → SubstTm t (wkSub {A = A} σ) (wkTm {A = A} u)
  substTm-wkSub (sub-var p) = sub-var (substVar-wkSub p)
  substTm-wkSub (sub-coh p) = sub-coh (compSub-wkSub p)

  compSub-wkSub : ∀ {Γ Δ Θ : RawCtx} {A : RawTy Γ} {τ : RawSub Δ Θ} {σ : RawSub Γ Δ} {υ : RawSub Γ Θ}
    → CompSub τ σ υ
    → CompSub τ (wkSub {A = A} σ) (wkSub {A = A} υ)
  compSub-wkSub comp-empty = comp-empty
  compSub-wkSub (comp-snoc p pt) =
    comp-snoc (compSub-wkSub p) (substTm-wkSub pt)
```

## Substitution, Lookup, and Composition

Substitution, lookup, and composition are mutually recursive. `lookup`
traverses a substitution by a de Bruijn index, `_[_]T` and `_[_]t` apply a
substitution to a type or term, and `_∘_` composes two substitutions.

```agda
mutual
  lookup : {Γ Δ : RawCtx} → RawVar Δ → RawSub Γ Δ → RawTm Γ
  lookup zero ⟨ σ , t ⟩ = t
  lookup (succ x) ⟨ σ , t ⟩ = lookup x σ

  _[_]T : {Γ Δ : RawCtx} → RawTy Δ → RawSub Γ Δ → RawTy Γ
  ⋆ [ σ ]T = ⋆
  ([ A ] t ⇒ u) [ σ ]T = [ A [ σ ]T ] t [ σ ]t ⇒ u [ σ ]t

  _[_]t : {Γ Δ : RawCtx} → RawTm Δ → RawSub Γ Δ → RawTm Γ
  var x [ σ ]t = lookup x σ
  coh A u v τ [ σ ]t = coh A u v (τ ∘ σ)

  _∘_ : {Γ Δ Θ : RawCtx} → RawSub Δ Θ → RawSub Γ Δ → RawSub Γ Θ
  ◆S ∘ σ = ◆S
  ⟨ τ , t ⟩ ∘ σ = ⟨ τ ∘ σ , t [ σ ]t ⟩
```

## Substitution Lemmas

These raw lemmas establish the standard equational theory of substitution.

```agda
lookup-∘ : {Γ Δ Θ : RawCtx} (x : RawVar Θ) (τ : RawSub Δ Θ) (σ : RawSub Γ Δ)
  → lookup x (τ ∘ σ) ≡ (lookup x τ) [ σ ]t
lookup-∘ zero    ⟨ τ , t ⟩ σ = refl
lookup-∘ (succ x) ⟨ τ , t ⟩ σ = lookup-∘ x τ σ

mutual
  assocS : {Γ Δ Θ Ξ : RawCtx} (γ : RawSub Θ Ξ) (τ : RawSub Δ Θ) (σ : RawSub Γ Δ)
    → γ ∘ (τ ∘ σ) ≡ (γ ∘ τ) ∘ σ
  assocS ◆S        τ σ = refl
  assocS ⟨ γ , t ⟩ τ σ = cong₂ ⟨_,_⟩ (assocS γ τ σ) ([∘]t t τ σ)

  [∘]t : {Γ Δ Θ : RawCtx} (t : RawTm Θ) (τ : RawSub Δ Θ) (σ : RawSub Γ Δ)
    → t [ τ ∘ σ ]t ≡ (t [ τ ]t) [ σ ]t
  [∘]t (var x)                τ σ = lookup-∘ x τ σ
  [∘]t (coh A u v τ')         τ σ = cong (coh A u v) (assocS τ' τ σ)

[∘]T : {Γ Δ Θ : RawCtx} (A : RawTy Θ) (τ : RawSub Δ Θ) (σ : RawSub Γ Δ)
  → A [ τ ∘ σ ]T ≡ (A [ τ ]T) [ σ ]T
[∘]T ⋆             τ σ = refl
[∘]T ([ A ] t ⇒ u) τ σ =
  trans
    (cong (λ A → [ A ] (t [ τ ∘ σ ]t) ⇒ (u [ τ ∘ σ ]t)) ([∘]T A τ σ))
    (cong₂ (λ s1 s2 → [ A [ τ ]T [ σ ]T ] s1 ⇒ s2) ([∘]t t τ σ) ([∘]t u τ σ))

mutual
  wkSub-∘ : {Γ Δ Θ : RawCtx} {A : RawTy Δ}
    (τ : RawSub Δ Θ) (σ : RawSub Γ Δ) (t : RawTm Γ) → wkSub {A = A} τ ∘ ⟨ σ , t ⟩ ≡ τ ∘ σ
  wkSub-∘ ◆S       σ t = refl
  wkSub-∘ ⟨ τ , u ⟩ σ t = cong₂ ⟨_,_⟩ (wkSub-∘ τ σ t) (wkTm-[]t u σ t)

  wkTm-[]t : {Γ Δ : RawCtx} {A : RawTy Δ}
    (u : RawTm Δ) (σ : RawSub Γ Δ) (t : RawTm Γ) → wkTm {A = A} u [ ⟨ σ , t ⟩ ]t ≡ u [ σ ]t
  wkTm-[]t (var x)                σ t = refl
  wkTm-[]t (coh A u v τ)          σ t = cong (coh A u v) (wkSub-∘ τ σ t)

wkTy-[]T : {Γ Δ : RawCtx} {B : RawTy Γ}
  (A : RawTy Γ) (σ : RawSub Δ Γ) (t : RawTm Δ) → wkTy {A = B} A [ ⟨ σ , t ⟩ ]T ≡ A [ σ ]T
wkTy-[]T ⋆              σ t = refl
wkTy-[]T ([ A ] u ⇒ v) σ t =
  trans
    (cong (λ B → [ B ] (wkTm u [ ⟨ σ , t ⟩ ]t) ⇒ (wkTm v [ ⟨ σ , t ⟩ ]t)) (wkTy-[]T A σ t))
    (cong₂ (λ s1 s2 → [ A [ σ ]T ] s1 ⇒ s2) (wkTm-[]t u σ t) (wkTm-[]t v σ t))

wkTy-rel-[]T : ∀ {Γ Δ : RawCtx} {B : RawTy Γ} {A : RawTy Γ} {A' : RawTy (Γ ▸ B)}
  → WkTy {A = B} A A'
  → (σ : RawSub Δ Γ)
  → (t : RawTm Δ)
  → A' [ ⟨ σ , t ⟩ ]T ≡ A [ σ ]T
wkTy-rel-[]T {A = A} p σ t =
  trans
    (cong (_[ ⟨ σ , t ⟩ ]T) (sym (wkTy-rel→≡ p)))
    (wkTy-[]T A σ t)

mutual
  [idS]T : {Γ : RawCtx} (A : RawTy Γ) → A [ idS Γ ]T ≡ A
  [idS]T ⋆              = refl
  [idS]T ([ A ] t ⇒ u) =
    trans
      (cong (λ B → [ B ] (t [ idS _ ]t) ⇒ (u [ idS _ ]t)) ([idS]T A))
      (cong₂ (λ s1 s2 → [ A ] s1 ⇒ s2) ([idS]t t) ([idS]t u))

  [idS]t : {Γ : RawCtx} (t : RawTm Γ) → t [ idS Γ ]t ≡ t
  [idS]t (var x)                = lookup-idS x
  [idS]t (coh A u v τ)          = cong (coh A u v) (∘-idS-r τ)

  lookup-idS : {Γ : RawCtx} (x : RawVar Γ) → lookup x (idS Γ) ≡ var x
  lookup-idS zero               = refl
  lookup-idS (succ {Γ = Γ} x)   = trans (lookup-wkSub x (idS Γ)) (cong wkTm (lookup-idS x))

  lookup-wkSub : {Γ Δ : RawCtx} {A : RawTy Γ} (x : RawVar Δ) (σ : RawSub Γ Δ)
    → lookup x (wkSub {A = A} σ) ≡ wkTm (lookup x σ)
  lookup-wkSub zero     ⟨ σ , t ⟩ = refl
  lookup-wkSub (succ x) ⟨ σ , t ⟩ = lookup-wkSub x σ

  ∘-idS-r : {Γ Δ : RawCtx} (σ : RawSub Γ Δ) → σ ∘ idS Γ ≡ σ
  ∘-idS-r ◆S       = refl
  ∘-idS-r ⟨ σ , t ⟩ = cong₂ ⟨_,_⟩ (∘-idS-r σ) ([idS]t t)

mutual
  wkSub-∘-r : {Γ Δ Θ : RawCtx} {A : RawTy Γ} (τ : RawSub Δ Θ) (σ : RawSub Γ Δ)
    → wkSub {A = A} (τ ∘ σ) ≡ τ ∘ wkSub {A = A} σ
  wkSub-∘-r ◆S       σ = refl
  wkSub-∘-r ⟨ τ , t ⟩ σ = cong₂ ⟨_,_⟩ (wkSub-∘-r τ σ) (wkTm-[]t-r t σ)

  wkTm-[]t-r : {Γ Δ : RawCtx} {B : RawTy Γ} (t : RawTm Δ) (σ : RawSub Γ Δ)
    → wkTm {A = B} (t [ σ ]t) ≡ t [ wkSub {A = B} σ ]t
  wkTm-[]t-r (var x)               σ = sym (lookup-wkSub x σ)
  wkTm-[]t-r (coh A u v τ)         σ = cong (coh A u v) (wkSub-∘-r τ σ)

wkTy-[]T-r : {Γ Δ : RawCtx} {B : RawTy Γ} (A : RawTy Δ) (σ : RawSub Γ Δ)
  → wkTy {A = B} (A [ σ ]T) ≡ A [ wkSub {A = B} σ ]T
wkTy-[]T-r ⋆             σ = refl
wkTy-[]T-r ([ A ] t ⇒ u) σ =
  trans
    (cong (λ X → [ X ] wkTm (t [ σ ]t) ⇒ wkTm (u [ σ ]t)) (wkTy-[]T-r A σ))
    (cong₂ (λ s1 s2 → [ A [ wkSub σ ]T ] s1 ⇒ s2) (wkTm-[]t-r t σ) (wkTm-[]t-r u σ))

hasTy-wk : ∀ {Γ : RawCtx} {B : RawTy Γ} {t : RawTm Γ} {A : RawTy Γ}
  → HasTy t A
  → HasTy (wkTm {A = B} t) (wkTy {A = B} A)
hasTy-wk {A = A} (varTy p) = varTy (succTy p (wkTy-rel A))
hasTy-wk (cohTy p) = cohTy (substTy-wkSub p)

hasTySub-wkSub : ∀ {Γ Δ : RawCtx} {C : RawTy Γ} {t : RawTm Γ} {A : RawTy Δ} {σ : RawSub Γ Δ}
  → HasTySub t A σ
  → HasTySub (wkTm {A = C} t) A (wkSub {A = C} σ)
hasTySub-wkSub (typed-sub s h) = typed-sub (substTy-wkSub s) (hasTy-wk h)

∘-idS-l : {Γ Δ : RawCtx} (σ : RawSub Γ Δ) → idS Δ ∘ σ ≡ σ
∘-idS-l ◆S        = refl
∘-idS-l ⟨ σ , t ⟩ = cong₂ ⟨_,_⟩ (trans (wkSub-∘ (idS _) σ t) (∘-idS-l σ)) refl

```

## Computed Typing Compatibility

The inductive typing relation from `1a-RawSyntax` is the primary interface.
These definitions retain the older computed typing view for downstream
compatibility code.

```agda
var-to-type : {Γ : RawCtx} → RawVar Γ → RawTy Γ
var-to-type {Γ = _ ▸ A} zero = wkTy A
var-to-type {Γ = _ ▸ A} (succ x) = wkTy (var-to-type x)

tyOf : {Γ : RawCtx} → RawTm Γ → RawTy Γ
tyOf (var x) = var-to-type x
tyOf (coh A u v σ) = ([ A ] u ⇒ v) [ σ ]T

mutual
  substVar : ∀ {Γ Δ : RawCtx} (x : RawVar Δ) (σ : RawSub Γ Δ)
    → SubstVar x σ (lookup x σ)
  substVar zero     ⟨ σ , t ⟩ = sub-zero
  substVar (succ x) ⟨ σ , t ⟩ = sub-succ (substVar x σ)

  substTy : ∀ {Γ Δ : RawCtx} (A : RawTy Δ) (σ : RawSub Γ Δ)
    → SubstTy A σ (A [ σ ]T)
  substTy ⋆             σ = sub-⋆
  substTy ([ A ] t ⇒ u) σ = sub-hom (substTy A σ) (substTm t σ) (substTm u σ)

  substTm : ∀ {Γ Δ : RawCtx} (t : RawTm Δ) (σ : RawSub Γ Δ)
    → SubstTm t σ (t [ σ ]t)
  substTm (var x)       σ = sub-var (substVar x σ)
  substTm (coh A u v τ) σ = sub-coh (compSub τ σ)

  compSub : ∀ {Γ Δ Θ : RawCtx} (τ : RawSub Δ Θ) (σ : RawSub Γ Δ)
    → CompSub τ σ (τ ∘ σ)
  compSub ◆S        σ = comp-empty
  compSub ⟨ τ , t ⟩ σ = comp-snoc (compSub τ σ) (substTm t σ)

mutual
  substVar→lookup≡ : ∀ {Γ Δ : RawCtx} {x : RawVar Δ} {σ : RawSub Γ Δ} {t : RawTm Γ}
    → SubstVar x σ t → lookup x σ ≡ t
  substVar→lookup≡ sub-zero     = refl
  substVar→lookup≡ (sub-succ p) = substVar→lookup≡ p

  substTy→[]T≡ : ∀ {Γ Δ : RawCtx} {A : RawTy Δ} {σ : RawSub Γ Δ} {B : RawTy Γ}
    → SubstTy A σ B → A [ σ ]T ≡ B
  substTy→[]T≡ sub-⋆ = refl
  substTy→[]T≡ (sub-hom pA pt pu)
    rewrite substTy→[]T≡ pA
          | substTm→[]t≡ pt
          | substTm→[]t≡ pu = refl

  substTm→[]t≡ : ∀ {Γ Δ : RawCtx} {t : RawTm Δ} {σ : RawSub Γ Δ} {u : RawTm Γ}
    → SubstTm t σ u → t [ σ ]t ≡ u
  substTm→[]t≡ (sub-var p) = substVar→lookup≡ p
  substTm→[]t≡ (sub-coh p) = cong (coh _ _ _) (compSub→∘≡ p)

  compSub→∘≡ : ∀ {Γ Δ Θ : RawCtx} {τ : RawSub Δ Θ} {σ : RawSub Γ Δ} {υ : RawSub Γ Θ}
    → CompSub τ σ υ → τ ∘ σ ≡ υ
  compSub→∘≡ comp-empty = refl
  compSub→∘≡ (comp-snoc p pt)
    rewrite compSub→∘≡ p
          | substTm→[]t≡ pt = refl

hasTyVar : ∀ {Γ : RawCtx} (x : RawVar Γ) → HasTyVar x (var-to-type x)
hasTyVar zero = zeroTy (wkTy-rel _)
hasTyVar (succ x) = succTy (hasTyVar x) (wkTy-rel _)

hasTy : ∀ {Γ : RawCtx} (t : RawTm Γ) → HasTy t (tyOf t)
hasTy (var x) = varTy (hasTyVar x)
hasTy (coh A u v σ) = cohTy (substTy ([ A ] u ⇒ v) σ)

hasTyVar→tyOf : ∀ {Γ : RawCtx} {x : RawVar Γ} {A : RawTy Γ}
  → HasTyVar x A
  → var-to-type x ≡ A
hasTyVar→tyOf (zeroTy p) = wkTy-rel→≡ p
hasTyVar→tyOf (succTy p q) =
  trans (cong wkTy (hasTyVar→tyOf p)) (wkTy-rel→≡ q)

hasTy→tyOf : ∀ {Γ : RawCtx} {t : RawTm Γ} {A : RawTy Γ}
  → HasTy t A
  → tyOf t ≡ A
hasTy→tyOf (varTy p) = hasTyVar→tyOf p
hasTy→tyOf (cohTy p) = substTy→[]T≡ p

tyOf≡→hasTy : ∀ {Γ : RawCtx} {t : RawTm Γ} {A : RawTy Γ}
  → tyOf t ≡ A
  → HasTy t A
tyOf≡→hasTy {t = t} p = subst (HasTy t) p (hasTy t)

computed-hasTySub : ∀ {Γ Δ : RawCtx} {t : RawTm Γ} {A : RawTy Δ} {σ : RawSub Γ Δ}
  → HasTy t (A [ σ ]T)
  → HasTySub t A σ
computed-hasTySub {A = A} {σ = σ} p = typed-sub (substTy A σ) p

hasTySub→computed : ∀ {Γ Δ : RawCtx} {t : RawTm Γ} {A : RawTy Δ} {σ : RawSub Γ Δ}
  → HasTySub t A σ
  → HasTy t (A [ σ ]T)
hasTySub→computed {t = t} (typed-sub q r) =
  subst (HasTy t) (sym (substTy→[]T≡ q)) r
```
