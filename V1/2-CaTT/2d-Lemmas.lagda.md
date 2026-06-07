# 2d-Lemmas: Dimension/Dependency Lemmas for CaTT

This module collects helper lemmas relating:
- semantic dependency (`depends-on-var-*`)
- dimensions (`dim-var`, `dim-tm`, `dim-ty`)
- boundary/fullness predicates from `2b-Wrappers`

It is the bridge between the computable boundary/fullness checks and the
dimension inequalities used in the functoriality proofs.

**Belongs here:** Dimension–dependency interaction lemmas, fullness bounds,
`∃-var-witness`, `dim-ty-sub`, quantifier erasure.
**Does NOT belong here:** Pure dependency lemmas without dimension (→ `2c-Dep`),
pure coherence/transport lemmas (→ `2e-SubstCoherence`), or functoriality-specific
constructions (→ `3-Functoriality`).

The main dependency-vs-dimension lemmas are now proved below, together with the
fullness bound and coherence corollary, in a single mutual block.

## Natural-Language Statements and Proof Sketches

Three lemmas mutually interact:

**Lemma 1 (fullness gives a dimension bound).**
Assume `Γ` is a pasting context, and `u , v : A` satisfy the fullness
condition. Then every variable `y : Var Γ` satisfies
`dim(y) ≤ dim(u) + 1`.

**Proof sketch.**
There are two fullness cases.
- In the **INV** case, `u` depends on every variable `y`, so Lemma 2 gives
  `dim(y) ≤ dim(u)`.
- In the **COMP** case, `u` depends on every variable in the source boundary.
  Using Lemma 2 on a source-boundary witness `z`, we get `dim(z) ≤ dim(u)`.
  A separate boundary lemma shows that every variable `y` is within one
  dimension step of some source-boundary variable, i.e. `dim(y) ≤ dim(z) + 1`.
  Combining these yields `dim(y) ≤ dim(u) + 1`.

**Corollary (coherence dimension bounds all variables of the base context).**
If `σ : Sub Δ Γ` and the same fullness assumptions hold, then every
`y : Var Γ` satisfies
`dim(y) ≤ dim(coh Γps A u v p q pf σ)`.

**Proof sketch.**
By construction, the coherence term has dimension `dim(u) + 1` (up to the
definitional/propositional equalities proved in this file). Apply Lemma 1.

**Lemma 2 (term dependency bounds variable dimension).**
If a term `t` semantically depends on a variable `x`, then
`dim(x) ≤ dim(t)`.

**Proof sketch.**
Proceed by induction on `t`.
- If `t = var y`, either `x = y` (so dimensions are equal), or `x` occurs in
  the declared type of `y`. In the latter case, Lemma 3 implies
  `dim(x) < dim(y) = dim(var y)`.
- If `t = coh Γps A u v p q pf σ`, dependency means some variable `y` in the
  source context of the coherence has image `y[σ]` depending on `x`.
  By induction, `dim(x) ≤ dim(y[σ])`. One also proves dimension invariance
  under substitution (`dim(y[σ]) = dim(y)`). It remains to bound `dim(y)` by
  the coherence dimension, which is exactly the corollary above.

**Lemma 3 (type dependency is strictly dimension-raising).**
If a type `A` semantically depends on `x`, then
`suc (dim(x)) ≤ dim(A)`.

**Proof sketch.**
Proceed by induction on `A`.
- If `A = ⋆`, the dependency premise is impossible.
- If `A = [ A' ] t ⇒ u :[ p , q ]`, then dependency means one of `A'`, `t`, or
  `u` depends on `x`.
  - If `A'` depends on `x`, apply the induction hypothesis and then weaken the
    inequality by one successor step.
  - If `t` or `u` depends on `x`, apply Lemma 2 to get `dim(x) ≤ dim(t)` or
    `dim(x) ≤ dim(u)`. Since the hom-type dimension is one more than the base
    type dimension, and `t,u` are endpoints of that base type, this yields the
    desired strict inequality.

These proofs are mutually entangled: Lemma 1 uses Lemma 2, while the coherence
case of Lemma 2 uses the corollary of Lemma 1, and the variable case of Lemma 2
uses Lemma 3. In code this is handled by a mutual block (plus a few auxiliary
helpers that recurse structurally on substitutions).

```agda
module 2d-Lemmas where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
import Relation.Binary.PropositionalEquality as Eq
open Eq using (sym; trans; cong; subst; _≡_; refl)
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _≤_; _∸_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; m∸n≤m)

open import 0a-Logic
import 1a-preCaTT as Pre renaming (_,_ to _▸_ ; ∅ to ◆)
import 1b-Dep as PreDep
import 1c-Pasting as PrePs
import 1d-Fullness as PreFull
open import 2b-Wrappers as Wrap renaming (_,_ to _▸_ ; _,_wf to ▸wf)
-- open import 2c-Dep
```

## Helper Lemmas

```agda
-- Constructive existential witness from boolean ∃-var = true.

pre-∃-var-witness :
  (Γ : Pre.Ctx)
  → (P : Pre.Var Γ → Bool)
  → Pre.∃-var Γ P ≡ true
  → Σ (Pre.Var Γ) (λ x → P x ≡ true)
pre-∃-var-witness (Γ Pre.▸ A) P p with P Pre.vz in pvz
... | true = Pre.vz , pvz
... | false = (Pre.vs (fst rec)) , (snd rec)
  where rec = pre-∃-var-witness Γ (λ x → P (Pre.vs x)) p

∃-var-witness :
  {Γ : Ctx}
  {P : Var Γ → Bool}
  → ∃-var Γ P ≡ true
  → Σ (Var Γ) (λ x → P x ≡ true)
∃-var-witness {Γ} {P} p = pre-∃-var-witness (Raw-Ctx Γ) P p

-- If check-COMP holds and z is in the source boundary, then u depends on z.
check-COMP-src-dep :
    {Γ : Ctx}
    → (Γps : Wrap.CtxPs Γ)
    → (u v : Tm Γ)
    → Wrap.check-COMP Γps u v ≡ true
    → (z : Var Γ)
    → Wrap.in-src-bdry {Γ} Γps z ≡ true
    → depends-on-var-tm z u ≡ true
check-COMP-src-dep Γps u v comp z zInSrc =
    iff-trueʳ→trueˡ (∧-trueˡ pointwise) zInSrc
  where
    pointwise = Pre.∀-var-elim comp z

-- If check-INV holds, then u depends on every variable y.
check-INV-left-dep :
    {Γ : Ctx}
    → (Γps : Wrap.CtxPs Γ)
    → (u v : Tm Γ)
    → Wrap.check-INV Γps u v ≡ true
    → (y : Var Γ)
    → depends-on-var-tm y u ≡ true
check-INV-left-dep Γps u v inv y =
    ∧-trueˡ (Pre.∀-var-elim inv y)

ctx≤suc-ctx∸1 : (n : ℕ) → n ≤ suc (n ∸ 1)
ctx≤suc-ctx∸1 zero = z≤n
ctx≤suc-ctx∸1 (suc n) = ≤-refl

-- Raw dimension counter (for transporting dimension along `toPreTy` equalities).
pre-dim-ty : ∀ {Γ} → Pre.Ty Γ → ℕ
pre-dim-ty Pre.⋆ = 0
-- Endpoint terms do not contribute to dimension, only the recursive base type.
pre-dim-ty (Pre.[ A ] t ⇒ u) = suc (pre-dim-ty A)

pre-dim-ty-sub :
  ∀ {Γ Δ} → (A : Pre.Ty Γ) → (σ : Pre.Sub Δ Γ)
  → pre-dim-ty (Pre._[_]T A σ) ≡ pre-dim-ty A
pre-dim-ty-sub Pre.⋆ σ = refl
pre-dim-ty-sub (Pre.[ A ] t ⇒ u) σ rewrite pre-dim-ty-sub A σ = refl

-- Raw preCaTT dimension counter agrees with the one from `1c-Pasting`.
Pre-dim-ty-toPre : ∀ {Γ} (A : Pre.Ty Γ) → PrePs.dim-ty A ≡ pre-dim-ty A
Pre-dim-ty-toPre Pre.⋆ = refl
Pre-dim-ty-toPre (Pre.[ A ] t ⇒ u) rewrite Pre-dim-ty-toPre A = refl

PrePs-dim-ty-sub :
  ∀ {Γ Δ} → (A : Pre.Ty Γ) → (σ : Pre.Sub Δ Γ)
  → PrePs.dim-ty (Pre._[_]T A σ) ≡ PrePs.dim-ty A
PrePs-dim-ty-sub A σ =
  trans (Pre-dim-ty-toPre (Pre._[_]T A σ))
    (trans (pre-dim-ty-sub A σ)
           (sym (Pre-dim-ty-toPre A)))

dim-ty-toPre : ∀ {Γ} (A : Ty Γ) → dim-ty A ≡ pre-dim-ty (Raw-Ty A)
dim-ty-toPre A = Pre-dim-ty-toPre (Raw-Ty A)

-- Wrapped term dimension agrees definitionally with the erased typing alias `tyOfTm`.
dim-tm-toPre-tyOf : ∀ {Γ} (t : Tm Γ) → dim-tm t ≡ pre-dim-ty (Raw-Ty (tyOf t))
dim-tm-toPre-tyOf t = Pre-dim-ty-toPre (Raw-Ty (tyOf t))

-- Type dimension is invariant under substitution.
dim-ty-sub : {Γ Δ : Ctx} → (A : Ty Γ) → (σ : Sub Δ Γ) → dim-ty (A [ σ ]T) ≡ dim-ty A
dim-ty-sub A σ = PrePs-dim-ty-sub (Raw-Ty A) (Raw-Sub σ)

-- Term dimension is also invariant under substitution.
dim-tm-sub :
  {Γ Δ : Ctx} → (t : Tm Γ) → (σ : Sub Δ Γ) → dim-tm (t [ σ ]t) ≡ dim-tm t
dim-tm-sub t σ =
  trans (dim-tm-toPre-tyOf (t [ σ ]t))
    (trans (cong pre-dim-ty (tyOf-comm (Raw-Tm t) (Pre.tyOf (Raw-Tm t)) (cast-sub σ) refl))
      (trans (pre-dim-ty-sub (Pre.tyOf (Raw-Tm t)) (Raw-Sub σ))
             (sym (dim-tm-toPre-tyOf t))))

-- If `u` has raw type equal to `A`, then their dimensions agree.
tm-PreTyEq→dim-tm≡dim-ty :
  {Γ : Ctx} → (u : Tm Γ) → (A : Ty Γ)
  → TmTyEq u A
  → dim-tm u ≡ dim-ty A
tm-PreTyEq→dim-tm≡dim-ty u A p =
  trans (dim-tm-toPre-tyOf u)
    (trans (cong pre-dim-ty p) (sym (dim-ty-toPre A)))

dim-tm-var-raw :
  ∀ {Γ} (x : Pre.Var Γ) → PrePs.dim-tm {Γ} (Pre.var x) ≡ PrePs.dim-var {Γ} x
dim-tm-var-raw x = refl

-- A variable term has the same dimension as the underlying variable.
dim-tm-var : ∀ {Γ} (x : Var Γ) → dim-tm {Γ} (var x) ≡ dim-var {Γ} x
dim-tm-var = dim-tm-var-raw

-- The top variable in an extended context has dimension equal to the declared type.
dim-var-vz : ∀ {Γ} {A : Ty Γ} → dim-var {Γ = Γ ▸ A} Pre.vz ≡ dim-ty A
dim-var-vz {Γ} {A} = PrePs.dim-ty-wkTy (Raw-Ty A)
-- Constructive witness for substitution dependency.
raw-depends-on-var-sub-witness :
  {Γ Δ : Pre.Ctx}
  → (x : Pre.Var Γ)
  → (σ : Pre.Sub Γ Δ)
  → PreDep.depends-on-var-sub x σ ≡ true
  → Σ (Pre.Var Δ) (λ y → PreDep.depends-on-var-sub-at x σ y ≡ true)
raw-depends-on-var-sub-witness {Γ} {Δ} x σ p =
  pre-∃-var-witness Δ (λ y → PreDep.depends-on-var-sub-at x σ y) p

depends-on-var-sub-witness :
  {Γ Δ : Ctx}
  → (x : Var Γ)
  → (σ : Sub Γ Δ)
  → depends-on-var-sub x σ ≡ true
  → Σ (Var Δ) (λ y → depends-on-var-sub-at x σ y ≡ true)
depends-on-var-sub-witness x σ p = raw-depends-on-var-sub-witness x (Raw-Sub σ) p 

-- Looking up a variable through a substitution does not change its dimension.
dim-lookup≡dim-var :
  {Γ Δ : Ctx}
  → (y : Var Γ)
  → (σ : Sub Δ Γ)
  → dim-tm (lookup y σ) ≡ dim-var {Γ} y
dim-lookup≡dim-var {Γ} y σ = trans (dim-tm-sub (var y) σ) (dim-tm-var {Γ} y)

dim-lookup≡dim-var-alt :
  {Γ Δ : Pre.Ctx}
  → {Γwf : Ctx-iswf Γ}
  → {Δwf : Ctx-iswf Δ}
  → (y : Pre.Var Γ)
  → (σ : Sub' Δ Γ)
  → PrePs.dim-tm (Pre.lookup y (Sub'.rawSub σ)) ≡ PrePs.dim-var y
dim-lookup≡dim-var-alt {Γ} {Δ} {Γwf} {Δwf} y σ =
  dim-lookup≡dim-var {mkCtx Γ Γwf} {mkCtx Δ Δwf} y (mkSub (Sub'.rawSub σ) (Sub'.sub-iswf σ))
```

## Dimension/Dependency Lemmas

```agda
-- Corollary (formalized): dim(coh .. σ) is at least suc(dim(u)).
suc-dim-u≤dim-coh :
  {Γ Δ : Ctx}
  → (Γps : Wrap.CtxPs Γ)
  → (A : Ty Γ)
  → (u v : Tm Γ)
  → (p : TmTyEq u A)
  → (q : TmTyEq v A)
  → (pf : Wrap.is-full Γps u v ≡ true)
  → (σ : Sub Δ Γ)
  → suc (dim-tm u) ≤ dim-tm (coh Γps A u v p q pf σ)
suc-dim-u≤dim-coh Γps A u v p q pf σ
  -- Rewrite the left side using the endpoint typing proof `p`,
  -- and the right side using dimension invariance under substitution.
  rewrite tm-PreTyEq→dim-tm≡dim-ty u A p
        | PrePs-dim-ty-sub (Raw-Ty A) (Raw-Sub σ)
  = ≤-refl
```

-- ## Fullness Consequences

```agda
full-false-COMP→INV :
  {Γ : Ctx}
  → (Γps : Wrap.CtxPs Γ)
  → (u v : Tm Γ)
  → Wrap.check-COMP Γps u v ≡ false
  → Wrap.is-full Γps u v ≡ true
  → Wrap.check-INV Γps u v ≡ true
full-false-COMP→INV Γps u v comp-false full-true with Wrap.check-INV Γps u v in inv
... | true = refl
-- If both COMP and INV are false, `is-full` would be false, contradiction.
... | false rewrite comp-false = true≠false (sym full-true)

{-# TERMINATING #-}
mutual
  var-dep→dim-var≤dim-var-alt : 
    (Γ : Pre.Ctx)
    → (Γwf : Ctx-iswf Γ) 
    → (x y : Pre.Var Γ)
    → PreDep.depends-on-var-tm x (Pre.var y) ≡ true
    → PrePs.dim-var x ≤ PrePs.dim-var y
  var-dep→dim-var≤dim-var-alt (Γ Pre.▸ A) (▸wf Γwf (mkTy A Awf)) Pre.vz Pre.vz dep = ≤-refl
  var-dep→dim-var≤dim-var-alt (Γ Pre.▸ A) (▸wf Γwf (mkTy A Awf)) (Pre.vs x) Pre.vz dep
    rewrite PrePs.dim-var-vs {A = A} x =
      ≤-trans (n≤1+n (PrePs.dim-var x))
        dimx<A
    where
      dimx<A : suc (PrePs.dim-var x) ≤ PrePs.dim-ty (Pre.wkTy A)
      dimx<A =
        subst
          (λ n → suc (PrePs.dim-var x) ≤ n)
          (sym (PrePs.dim-ty-wkTy A))
          (depends-on-var-ty→suc-dim-var≤dim-ty-alt {Γ} {Γwf} x (mkTy A Awf) dep)
  var-dep→dim-var≤dim-var-alt (Γ Pre.▸ A) (▸wf Γwf _) (Pre.vs x) (Pre.vs y) dep
    rewrite PrePs.dim-var-vs {A = A} x | PrePs.dim-var-vs {A = A} y =
      var-dep→dim-var≤dim-var-alt Γ Γwf x y dep

  -- Variable case helper for Lemma 2.
  var-dep→dim-var≤dim-var :
    {Γ : Ctx}
    → (x y : Var Γ)
    → depends-on-var-tm {Γ} x (var y) ≡ true
    → dim-var {Γ} x ≤ dim-var {Γ} y
  var-dep→dim-var≤dim-var {Γ} x y dep =
    var-dep→dim-var≤dim-var-alt (Raw-Ctx Γ) (Ctx-wf Γ) x y dep

  depends-on-var-sub-at→dim-var≤dim-tm-lookup-alt :
    {Γ Δ : Pre.Ctx}
    → {Γwf : Ctx-iswf Γ}
    → (x : Pre.Var Γ)
    → (σ : Sub' Γ Δ)
    → (y : Pre.Var Δ)
    → PreDep.depends-on-var-sub-at x (Sub'.rawSub σ) y ≡ true
    → PrePs.dim-var x ≤ PrePs.dim-tm (Pre.lookup y (Sub'.rawSub σ))
  depends-on-var-sub-at→dim-var≤dim-tm-lookup-alt {Γwf = Γwf} x σ y dep =
    depends-on-var-tm→dim-var≤dim-tm-alt {Γwf = Γwf} x (lookup' y σ)
      (trans (sym (PreDep.depends-on-var-sub-at-lookup x (Sub'.rawSub σ) y)) dep)

  -- Substitution-pointwise version used in the coherence case of Lemma 2.
  depends-on-var-sub-at→dim-var≤dim-tm-lookup :
    {Γ Δ : Ctx}
    → (x : Var Γ)
    → (σ : Sub Γ Δ)
    → (y : Var Δ)
    → depends-on-var-sub-at x σ y ≡ true
    → dim-var {Γ} x ≤ dim-tm (lookup y σ)
  depends-on-var-sub-at→dim-var≤dim-tm-lookup {Γ} x σ y dep =
    depends-on-var-sub-at→dim-var≤dim-tm-lookup-alt {Γwf = Ctx-wf Γ} x (cast-sub σ) y dep

  depends-on-var-tm→dim-var≤dim-tm-alt :
    {Γ : Pre.Ctx}
    → {Γwf : Ctx-iswf Γ}
    → (x : Pre.Var Γ)
    → (t : Tm' Γ)
    → PreDep.depends-on-var-tm x (Tm'.rawTm t) ≡ true
    → PrePs.dim-var {Γ} x ≤ PrePs.dim-tm (Tm'.rawTm t)
  depends-on-var-tm→dim-var≤dim-tm-alt {Γ} {Γwf} x (mkTm (Pre.var y) p) dep
    rewrite dim-tm-var-raw {Γ} y = var-dep→dim-var≤dim-var-alt Γ Γwf x y dep
  depends-on-var-tm→dim-var≤dim-tm-alt {Γ} {Γwf} x
    (mkTm (Pre.coh-raw A u v σ) (coh-wf {Δ = Δ} ps wf (mkTy .A Awf) (mkTm .u uwf) (mkTm .v vwf) p q r (mkSub .σ σwf))) dep
    with raw-depends-on-var-sub-witness x σ dep
  ... | y , dep-at =
    ≤-trans dimx≤lookup (≤-trans lookup≤y y≤coh)
    where
      dimx≤lookup = depends-on-var-sub-at→dim-var≤dim-tm-lookup-alt {Γwf = Γwf} x (mkSub σ σwf) y dep-at
      lookup≤y : PrePs.dim-tm (Pre.lookup y σ) ≤ PrePs.dim-var y
      lookup≤y rewrite dim-lookup≡dim-var-alt {Γwf = wf} {Δwf = Γwf} y (mkSub σ σwf) = ≤-refl
      y≤coh =
        full-coh-dim-bound-alt {Γwf = wf} {Δwf = Γwf}
          ps (mkTy A Awf) (mkTm u uwf) (mkTm v vwf) p q r (mkSub σ σwf) y

  -- Lemma 2 (formalized): term dependency bounds variable dimension from above.
  depends-on-var-tm→dim-var≤dim-tm :
    {Γ : Ctx}
    → (x : Var Γ)
    → (t : Tm Γ)
    → depends-on-var-tm x t ≡ true
    → dim-var {Γ} x ≤ dim-tm t
  depends-on-var-tm→dim-var≤dim-tm {Γ} x t dep =
    depends-on-var-tm→dim-var≤dim-tm-alt {Raw-Ctx Γ} {Ctx-wf Γ} x (mkTm (Raw-Tm t) (Tm-wf t)) dep

  depends-on-var-ty→suc-dim-var≤dim-ty-alt :
    {Γ : Pre.Ctx}
    → {Γwf : Ctx-iswf Γ} 
    → (x : Var (mkCtx Γ Γwf))
    → (A : Ty (mkCtx Γ Γwf))
    → depends-on-var-ty x A ≡ true
    → suc (PrePs.dim-var x) ≤ dim-ty A
  depends-on-var-ty→suc-dim-var≤dim-ty-alt {Γ} {Γwf} x (mkTy Pre.⋆ ⋆wf) ()
  depends-on-var-ty→suc-dim-var≤dim-ty-alt {Γ} {Γwf}
    x
    (mkTy (Pre.[ A ] t ⇒ u) (hom-wf (mkTy .A Awf) {mkTm .t twf} {mkTm .u uwf} p q))
    dep
    with depends-on-var-ty x (mkTy {Γ = mkCtx Γ Γwf} A Awf) in depA
       | depends-on-var-tm x (mkTm {Γ = mkCtx Γ Γwf} t twf) in dep-t
       | depends-on-var-tm x (mkTm {Γ = mkCtx Γ Γwf} u uwf) in dep-u
  ... | true  | _     | _     =
    ≤-trans
      (depends-on-var-ty→suc-dim-var≤dim-ty-alt {Γ} {Γwf} x (mkTy {Γ = mkCtx Γ Γwf} A Awf) depA)
      (n≤1+n (dim-ty (mkTy {Γ = mkCtx Γ Γwf} A Awf)))
  ... | false | true  | _     =
    s≤s dimx≤A
    where
      dimx≤A : PrePs.dim-var x ≤ dim-ty (mkTy {Γ = mkCtx Γ Γwf} A Awf)
      dimx≤A rewrite sym
        (tm-PreTyEq→dim-tm≡dim-ty
          (mkTm {Γ = mkCtx Γ Γwf} t twf)
          (mkTy {Γ = mkCtx Γ Γwf} A Awf) p) =
        depends-on-var-tm→dim-var≤dim-tm-alt
          {Γ = Γ} {Γwf = Γwf} x (mkTm {Γ = Γ} t twf) dep-t
  ... | false | false | true  =
    s≤s dimx≤A
    where
      dimx≤A : PrePs.dim-var x ≤ dim-ty (mkTy {Γ = mkCtx Γ Γwf} A Awf)
      dimx≤A rewrite sym
        (tm-PreTyEq→dim-tm≡dim-ty
          (mkTm {Γ = mkCtx Γ Γwf} u uwf)
          (mkTy {Γ = mkCtx Γ Γwf} A Awf) q) =
        depends-on-var-tm→dim-var≤dim-tm-alt
          {Γ = Γ} {Γwf = Γwf} x (mkTm {Γ = Γ} u uwf) dep-u
  ... | false | false | false =
    true≠false (sym dep)


  -- Lemma 3 (formalized): type dependency is strictly dimension-raising.
  depends-on-var-ty→suc-dim-var≤dim-ty :
    {Γ : Ctx}
    → (x : Var Γ)
    → (A : Ty Γ)
    → depends-on-var-ty x A ≡ true
    → suc (dim-var {Γ} x) ≤ dim-ty A
  depends-on-var-ty→suc-dim-var≤dim-ty {Γ} x A dep =
    depends-on-var-ty→suc-dim-var≤dim-ty-alt {Raw-Ctx Γ} {Ctx-wf Γ} x A dep

  -- Lemma 1 (formalized): fullness gives dim(u)+1 bound on all variables in Γ.
  full-dim+1-bound-alt :
    {Γ : Pre.Ctx}
    → {Γwf : Ctx-iswf Γ}
    → (Γps : Wrap.CtxPs (mkCtx Γ Γwf))
    → (A : Ty (mkCtx Γ Γwf))
    → (u v : Tm (mkCtx Γ Γwf))
    → .(p : TmTyEq u A)
    → .(q : TmTyEq v A)
    → (pf : Wrap.is-full Γps u v ≡ true)
    → (y : Pre.Var Γ)
    → PrePs.dim-var {Γ} y ≤ suc (dim-tm u)
  full-dim+1-bound-alt {Γ} {Γwf} Γps A u v p q pf y
    with Wrap.check-COMP Γps u v in eqComp
       | PreFull.src-bdry-i-has-dim Γps (Wrap.dim-ctx (mkCtx Γ Γwf) ∸ 1) (m∸n≤m (Wrap.dim-ctx (mkCtx Γ Γwf)) 1)
  ... | true  | zᵖ , (zInSrc-i , zDimᵖ) =
    ≤-trans dimy≤sucz (s≤s dimz≤u)
    where
      z : Pre.Var Γ
      z = zᵖ

      zInSrc : Wrap.in-src-bdry {mkCtx Γ Γwf} Γps z ≡ true
      zInSrc = zInSrc-i

      dep-z : depends-on-var-tm z u ≡ true
      dep-z = check-COMP-src-dep Γps u v eqComp z zInSrc

      dimz≤u : PrePs.dim-var {Γ} z ≤ dim-tm u
      dimz≤u = depends-on-var-tm→dim-var≤dim-tm-alt {Γ = Γ} {Γwf = Γwf} z (mkTm (Raw-Tm u) (Tm-wf u)) dep-z

      zDim : PrePs.dim-var {Γ} z ≡ (Wrap.dim-ctx (mkCtx Γ Γwf) ∸ 1)
      zDim = zDimᵖ

      dimy≤sucz : PrePs.dim-var {Γ} y ≤ suc (PrePs.dim-var {Γ} z)
      dimy≤sucz rewrite zDim =
        ≤-trans (PrePs.dim-var≤dim-ctx y) (ctx≤suc-ctx∸1 (Wrap.dim-ctx (mkCtx Γ Γwf)))
  ... | false | _ =
    ≤-trans dimy≤u (n≤1+n (dim-tm u))
    where
      inv-true : Wrap.check-INV Γps u v ≡ true
      inv-true with Wrap.check-INV Γps u v in inv
      ... | true = refl
      ... | false = true≠false (sym pf)

      dep-y : depends-on-var-tm y u ≡ true
      dep-y = check-INV-left-dep Γps u v inv-true y

      dimy≤u : PrePs.dim-var {Γ} y ≤ dim-tm u
      dimy≤u = depends-on-var-tm→dim-var≤dim-tm-alt {Γ = Γ} {Γwf = Γwf} y (mkTm (Raw-Tm u) (Tm-wf u)) dep-y

  -- Corollary: dim(coh .. σ) bounds all variables of Γ.
  full-coh-dim-bound-alt :
    {Γ Δ : Pre.Ctx}
    → {Γwf : Ctx-iswf Γ}
    → {Δwf : Ctx-iswf Δ}
    → (Γps : Wrap.CtxPs (mkCtx Γ Γwf))
    → (A : Ty (mkCtx Γ Γwf))
    → (u v : Tm (mkCtx Γ Γwf))
    → (p : TmTyEq u A)
    → (q : TmTyEq v A)
    → (pf : Wrap.is-full Γps u v ≡ true)
    → (σ : Sub (mkCtx Δ Δwf) (mkCtx Γ Γwf))
    → (y : Pre.Var Γ)
    → PrePs.dim-var {Γ} y ≤ dim-tm (coh Γps A u v p q pf σ)
  full-coh-dim-bound-alt Γps A u v p q pf σ y =
    ≤-trans (full-dim+1-bound-alt Γps A u v p q pf y)
           (suc-dim-u≤dim-coh Γps A u v p q pf σ)

  full-dim+1-bound :
    {Γ : Ctx}
    → (Γps : Wrap.CtxPs Γ)
    → (A : Ty Γ)
    → (u v : Tm Γ)
    → .(p : TmTyEq u A)
    → .(q : TmTyEq v A)
    → (pf : Wrap.is-full Γps u v ≡ true)
    → (y : Var Γ)
    → dim-var {Γ} y ≤ suc (dim-tm u)
  full-dim+1-bound {Γ} Γps A u v p q pf y =
    full-dim+1-bound-alt {Γ = Raw-Ctx Γ} {Γwf = Ctx-wf Γ} Γps A u v p q pf y

  full-coh-dim-bound :
    {Γ Δ : Ctx}
    → (Γps : Wrap.CtxPs Γ)
    → (A : Ty Γ)
    → (u v : Tm Γ)
    → (p : TmTyEq u A)
    → (q : TmTyEq v A)
    → (pf : Wrap.is-full Γps u v ≡ true)
    → (σ : Sub Δ Γ)
    → (y : Var Γ)
    → dim-var {Γ} y ≤ dim-tm (coh Γps A u v p q pf σ)
  full-coh-dim-bound {Γ} {Δ} Γps A u v p q pf σ y =
    full-coh-dim-bound-alt
      {Γwf = Ctx-wf Γ}
      {Δwf = Ctx-wf Δ}
      Γps A u v p q pf σ y
```

## Quantifier Erasure Correspondence

```agda
∀-var-toPre :
  ∀ {Γ} (P : Var Γ → Bool)
  → ∀-var Γ P ≡ Pre.∀-var (Raw-Ctx Γ) (λ x → P x)
∀-var-toPre {mkCtx Pre.◆ ◆wf} P = refl
∀-var-toPre {mkCtx (Γ Pre.▸ A) (▸wf Γwf A0)} P =
  cong (λ b → P Pre.vz ∧ b)
       (∀-var-toPre {mkCtx Γ Γwf} (λ x → P (Pre.vs x)))

pre-∀-var-cong :
  ∀ {Γ : Pre.Ctx} {P Q : Pre.Var Γ → Bool}
  → (∀ x → P x ≡ Q x)
  → Pre.∀-var Γ P ≡ Pre.∀-var Γ Q
pre-∀-var-cong {Γ = Pre.◆} h = refl
pre-∀-var-cong {Γ = Γ Pre.▸ A} h
  rewrite h Pre.vz
        | pre-∀-var-cong (λ x → h (Pre.vs x))
  = refl
```
