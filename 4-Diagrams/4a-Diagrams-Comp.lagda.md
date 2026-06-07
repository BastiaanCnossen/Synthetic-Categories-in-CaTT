# 4a-Diagrams-Comp: computed diagram operations (instances of the relations)

This is the computational companion to `4a-Diagrams`. The relational core defines
diagram types/terms and the **relations** that recognize diagram weakening, diagram
substitution, and the structural evaluators (`SubstDTy`, `SubstDTm`, `DWkTy`,
`SubstTyAtDTm`, …) — all with their outputs as explicit indices.

This module adds the corresponding **computed functions** (`dty-proj`, `_[_]dT` /
`dty-liftS`, `dtm-sub`, diagram weakening, …) — ported from the original
`4a-Diagrams` — together with **satisfaction lemmas** proving that each computed output
is recognized by the matching relation (the `*-rel` lemmas), in the style of
`1a-RawSyntax-Comp`'s `WkTy`/`SubstTy`/`CompSub` instances.

It is free to import the `-Comp` cores. The relational core is re-exported, so
importing this module gives both the relations and the computed operations.

```agda
module 4a-Diagrams-Comp where

open import 4a-Diagrams public
import 1a-RawSyntax-Comp as Raw
open import 2a-CaTT-Comp
open import 1z-Uniqueness using (wkSub-unique)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Product using (Σ; _,_; Σ-syntax)

infixl 8 _[_]dT
```

## Diagram projection

`dty-proj D : Sub (Γ ▸▸ D) Γ` projects the total context of a diagram telescope back to
the ambient context, by iterating single-step weakening.

```agda
dty-proj : {Γ : Ctx} → (D : DTy Γ) → Sub (Γ ▸▸ D) Γ
dty-proj {Γ} ◆ᵈ = idS Γ
dty-proj (D ▸ᵈ A) = dty-proj D ∘ wk {A = A}
```

## Diagram-type substitution

Substituting `σ : Δ → Γ` into a diagram telescope `D : DTy Γ` yields `D [ σ ]dT : DTy Δ`,
with the **lifted total substitution** `dty-liftS σ D : Sub (Δ ▸▸ (D [ σ ]dT)) (Γ ▸▸ D)`.

```agda
mutual
  _[_]dT : {Γ Δ : Ctx} → DTy Γ → Sub Δ Γ → DTy Δ
  ◆ᵈ [ σ ]dT = ◆ᵈ
  (D ▸ᵈ A) [ σ ]dT = (D [ σ ]dT) ▸ᵈ (A [ dty-liftS σ D ]T)

  dty-liftS : {Γ Δ : Ctx} → (σ : Sub Δ Γ) → (D : DTy Γ) →
    Sub (Δ ▸▸ (D [ σ ]dT)) (Γ ▸▸ D)
  dty-liftS σ ◆ᵈ = σ
  dty-liftS σ (D ▸ᵈ A) =
    ⟨ dty-liftS σ D ∘ wk {A = A [ dty-liftS σ D ]T}
       , vz {A = A [ dty-liftS σ D ]T}
       ⟩:[ vz-snoc-sub-hasTySub _ A (dty-liftS σ D) ]
```

`substDTy-rel` is the satisfaction lemma: the computed `_[_]dT` / `dty-liftS` are
recognized by the relation `SubstDTy`. The snoc step bridges the computed weakening
`ρ ∘ wk` to `Raw.WkSub` (via `Raw.wkSub-rel` and `wkSub-∘-r`) and the computed
substitution `A [ ρ ]T` to `Raw.SubstTy` (via `Raw.substTy`); the head typing is the
same `vz-snoc-sub-hasTySub` used to build `dty-liftS`.

```agda
substDTy-rel : {Γ Δ : Ctx} → (σ : Sub Δ Γ) → (D : DTy Γ) →
  SubstDTy σ D (D [ σ ]dT) (dty-liftS σ D)
substDTy-rel σ ◆ᵈ = ◆ˢ
substDTy-rel σ (D ▸ᵈ A) =
  let ρ  = dty-liftS σ D
      A′ = A [ ρ ]T
  in _▸ˢ_[_][_] {A = A} {A′ = A′} {ρwk = ρ ∘ wk {A = A′}}
       (substDTy-rel σ D)
       (subst (Raw.WkSub (Raw-Sub ρ))
              (cong Raw-Sub (wkSub-∘-r {A = A′} ρ))
              (Raw.wkSub-rel {A = Raw-Ty A′} (Raw-Sub ρ)))
       (Raw.substTy (Raw-Ty A) (Raw-Sub ρ))
       (vz-snoc-sub-hasTySub _ A ρ)
```

## Diagram-term substitution (the section of a diagram term)

`dtm-sub d : Sub Γ (Γ ▸▸ D)` turns a diagram term into the corresponding section. The
new `DTm` carries its entry typing *relationally* (`SubstTyAtDTm d A A′` + `HasTy a A′`),
so the snoc step must rebuild the computed `HasTySub a A (dtm-sub d)`. For that we prove,
mutually with `dtm-sub`, that each structural evaluator (`SubstTyAtDTm`/`SubstTmAtDTm`/
`SubstSubAtDTm`/`SubstVarAtDTm`) is **sound** for substitution along `dtm-sub d` — stated
at the raw level (where hom-types carry no proofs, so the congruences are clean).

```agda
mutual
  dtm-sub : {Γ : Ctx} {D : DTy Γ} → DTm D → Sub Γ (Γ ▸▸ D)
  dtm-sub {Γ} ◆ᵗ = idS Γ
  dtm-sub (_▸ᵗ_[_][_] {A = A} {A′ = A′} d a p q) =
    ⟨ dtm-sub d , a ⟩:[
      Raw.typed-sub
        (subst (Raw.SubstTy (Raw-Ty A) (Raw-Sub (dtm-sub d)))
               (substTyAtDTm-sound-raw d p)
               (Raw.substTy (Raw-Ty A) (Raw-Sub (dtm-sub d))))
        q ]

  substTyAtDTm-sound-raw :
    {Γ : Ctx} {D : DTy Γ} {A : Ty (Γ ▸▸ D)} {A′ : Ty Γ} →
    (d : DTm D) → SubstTyAtDTm d A A′ →
    Raw-Ty A Raw.[ Raw-Sub (dtm-sub d) ]T ≡ Raw-Ty A′
  substTyAtDTm-sound-raw d sty-⋆ = refl
  substTyAtDTm-sound-raw d (sty-hom {A′ = A′} pA pt pu) =
    trans
      (cong (λ B → Raw.[ B ] _ ⇒ _) (substTyAtDTm-sound-raw d pA))
      (cong₂ (λ s1 s2 → Raw.[ Raw-Ty A′ ] s1 ⇒ s2)
             (substTmAtDTm-sound-raw d pt) (substTmAtDTm-sound-raw d pu))

  substTmAtDTm-sound-raw :
    {Γ : Ctx} {D : DTy Γ} {t : Tm (Γ ▸▸ D)} {t′ : Tm Γ} →
    (d : DTm D) → SubstTmAtDTm d t t′ →
    Raw-Tm t Raw.[ Raw-Sub (dtm-sub d) ]t ≡ Raw-Tm t′
  substTmAtDTm-sound-raw d (stm-var sv) = substVarAtDTm-sound-raw d sv
  substTmAtDTm-sound-raw d (stm-coh {A = A} {u = u} {v = v} ss) =
    cong (λ ρ → Raw.coh (Raw-Ty A) (Raw-Tm u) (Raw-Tm v) ρ)
         (substSubAtDTm-sound-raw d ss)

  substSubAtDTm-sound-raw :
    {Γ : Ctx} {D : DTy Γ} {Δ : Ctx} {τ : Sub (Γ ▸▸ D) Δ} {τ′ : Sub Γ Δ} →
    (d : DTm D) → SubstSubAtDTm d τ τ′ →
    Raw-Sub τ Raw.∘ Raw-Sub (dtm-sub d) ≡ Raw-Sub τ′
  substSubAtDTm-sound-raw d ssub-◆ = refl
  substSubAtDTm-sound-raw d (ssub-snoc ss stm) =
    cong₂ Raw.⟨_,_⟩ (substSubAtDTm-sound-raw d ss) (substTmAtDTm-sound-raw d stm)

  substVarAtDTm-sound-raw :
    {Γ : Ctx} {D : DTy Γ} {x : Var (Γ ▸▸ D)} {t′ : Tm Γ} →
    (d : DTm D) → SubstVarAtDTm d x t′ →
    Raw.lookup x (Raw-Sub (dtm-sub d)) ≡ Raw-Tm t′
  substVarAtDTm-sound-raw .◆ᵗ (sv-base {x}) = Raw.lookup-idS x
  substVarAtDTm-sound-raw .(_ ▸ᵗ _ [ _ ][ _ ]) sv-zero = refl
  substVarAtDTm-sound-raw .(d ▸ᵗ _ [ _ ][ _ ]) (sv-succ {d = d} rec) =
    substVarAtDTm-sound-raw d rec
```

## Weakening along a diagram projection

Weakening a type / term / substitution along the projection `Γ ▸▸ D → Γ` is the iterated
single-step weakening. Each computed function comes with its `DWk*-rel` satisfaction
lemma against the relational core. In particular `dwkTm-fun` / `dwkTm-rel` are what the
diagram-hom construction uses to view the entry terms `aᵢ : Tm Γ` as terms of `Γ ▸▸ H`.

```agda
dwkTy-fun : {Γ : Ctx} → (D : DTy Γ) → Ty Γ → Ty (Γ ▸▸ D)
dwkTy-fun ◆ᵈ B = B
dwkTy-fun (D ▸ᵈ A) B = wkTy {A = A} (dwkTy-fun D B)

dwkTy-rel : {Γ : Ctx} → (D : DTy Γ) → (B : Ty Γ) → DWkTy D B (dwkTy-fun D B)
dwkTy-rel ◆ᵈ B = dwkTy-◆
dwkTy-rel (D ▸ᵈ A) B =
  dwkTy-▸ (dwkTy-rel D B) (Raw.wkTy-rel (Raw-Ty (dwkTy-fun D B)))

dwkTm-fun : {Γ : Ctx} → (D : DTy Γ) → Tm Γ → Tm (Γ ▸▸ D)
dwkTm-fun ◆ᵈ t = t
dwkTm-fun (D ▸ᵈ A) t = wkTm {A = A} (dwkTm-fun D t)

dwkTm-rel : {Γ : Ctx} → (D : DTy Γ) → (t : Tm Γ) → DWkTm D t (dwkTm-fun D t)
dwkTm-rel ◆ᵈ t = dwkTm-◆
dwkTm-rel (D ▸ᵈ A) t =
  dwkTm-▸ (dwkTm-rel D t) (Raw.wkTm-rel (Raw-Tm (dwkTm-fun D t)))

dwkSub-fun : {Γ Δ : Ctx} → (D : DTy Γ) → Sub Γ Δ → Sub (Γ ▸▸ D) Δ
dwkSub-fun ◆ᵈ σ = σ
dwkSub-fun (D ▸ᵈ A) σ = wkSub {A = A} (dwkSub-fun D σ)

dwkSub-rel : {Γ Δ : Ctx} → (D : DTy Γ) → (σ : Sub Γ Δ) → DWkSub D σ (dwkSub-fun D σ)
dwkSub-rel ◆ᵈ σ = dwkSub-◆
dwkSub-rel (D ▸ᵈ A) σ =
  dwkSub-▸ (dwkSub-rel D σ) (Raw.wkSub-rel (Raw-Sub (dwkSub-fun D σ)))
```

Diagram weakening of a *typed* term is substitution along the projection: weakening
`t : Tm Γ` of type `A` across `H` gives a term of `Γ ▸▸ H` whose type is `A` reindexed
along `dty-proj H`. This is the `HasTySub` witness the diagram-hom comparison needs to
type the two endpoint terms. `dwkTm-fun-proj` records the underlying definitional fact
`dwkTm-fun H t ≡ t [ dty-proj H ]t` (iterated single weakening equals substitution along
the projection).

```agda
dwkTm-fun-proj :
  {Γ : Ctx} (H : DTy Γ) (t : Tm Γ) → dwkTm-fun H t ≡ t [ dty-proj H ]t
dwkTm-fun-proj ◆ᵈ t = sym ([]t-id t)
dwkTm-fun-proj (H₀ ▸ᵈ A₀) t =
  trans (sym (wkTm-sub {A = A₀} (dwkTm-fun H₀ t)))
    (trans (cong (_[ wk {A = A₀} ]t) (dwkTm-fun-proj H₀ t))
      ([]t-∘ {t = t} {τ = dty-proj H₀} {σ = wk {A = A₀}}))

dwkTm-hasTySub :
  {Γ : Ctx} (H : DTy Γ) {t : Tm Γ} {A : Ty Γ} →
  HasTy t A → HasTySub (dwkTm-fun H t) A (dty-proj H)
dwkTm-hasTySub ◆ᵈ {t} {A} q =
  Raw.computed-hasTySub (subst (Raw.HasTy (Raw-Tm t)) (cong Raw-Ty (sym ([]T-id A))) q)
dwkTm-hasTySub (H₀ ▸ᵈ A₀) {t} {A} q =
  subst (λ u → HasTySub u A (dty-proj H₀ ∘ wk {A = A₀}))
    (wkTm-sub {A = A₀} (dwkTm-fun H₀ t))
    (hasTySub-sub {t = dwkTm-fun H₀ t} {A = A} {τ = dty-proj H₀} {σ = wk {A = A₀}}
       (dwkTm-hasTySub H₀ {t = t} {A = A} q))
```

## The action of a relative section

A relative section `d : DTmOverDTy D E` re-bases syntax living over the target diagram
context `Γ ▸▸ E` to syntax over the source diagram context `Γ ▸▸ D`. Its **underlying
substitution** `dover-sub d : Sub (Γ ▸▸ D) (Γ ▸▸ E)` makes this functional: the empty
section is the diagram projection, and each entry snocs its stored head term. The head's
`HasTySub` premise is rebuilt from the stored entry-evaluation evidence, exactly as
`dtm-sub` does for plain diagram terms.

```agda
-- Lookup of an ambient variable along a diagram projection is its iterated weakening.
dwkTm-proj-lookup-raw :
  {Γ : Ctx} (D : DTy Γ) {x : Var Γ} {t′ : Tm (Γ ▸▸ D)} →
  DWkTm D (var x) t′ →
  Raw.lookup x (Raw-Sub (dty-proj D)) ≡ Raw-Tm t′
dwkTm-proj-lookup-raw .◆ᵈ {x} dwkTm-◆ = Raw.lookup-idS x
dwkTm-proj-lookup-raw {Γ = Γ} .(D₀ ▸ᵈ A) {x} (dwkTm-▸ {D = D₀} {A = A} {t′ = t₀} w₀ rw) =
  trans
    (Raw.lookup-∘ x (Raw-Sub (dty-proj D₀)) (Raw-Sub (wk {A = A})))
    (trans
      (cong (Raw._[ Raw-Sub (wk {A = A}) ]t) (dwkTm-proj-lookup-raw D₀ w₀))
      (trans
        (sym (Raw.wkTm-[]t-r (Raw-Tm t₀) (Raw.idS (Raw-Ctx (Γ ▸▸ D₀)))))
        (trans
          (cong Raw.wkTm (Raw.[idS]t (Raw-Tm t₀)))
          (Raw.wkTm-rel→≡ rw))))
```

`dover-sub` is defined mutually with the **raw soundness** lemmas: substituting the
entry syntax along `dover-sub d` produces exactly the evaluated syntax recognized by the
section's `DSubst*Over` evidence. The structure mirrors `dtm-sub` and its
`substTyAtDTm-sound-raw` family, with the variable leaf using the projection-lookup
lemma above instead of `lookup-idS`.

```agda
mutual
  dover-sub :
    {Γ : Ctx} {D E : DTy Γ} → DTmOverDTy D E → Sub (Γ ▸▸ D) (Γ ▸▸ E)
  dover-sub {D = D} ◆ᴰ = dty-proj D
  dover-sub (_▸ᴰ_[_][_] {A = A} {A′ = A′} d a p q) =
    ⟨ dover-sub d , a ⟩:[
      Raw.typed-sub
        (subst (Raw.SubstTy (Raw-Ty A) (Raw-Sub (dover-sub d)))
               (dsubstTyOver-sound-raw d p)
               (Raw.substTy (Raw-Ty A) (Raw-Sub (dover-sub d))))
        q ]

  dsubstTyOver-sound-raw :
    {Γ : Ctx} {D E : DTy Γ} {A : Ty (Γ ▸▸ E)} {A′ : Ty (Γ ▸▸ D)} →
    (d : DTmOverDTy D E) → DSubstTyOver d A A′ →
    Raw-Ty A Raw.[ Raw-Sub (dover-sub d) ]T ≡ Raw-Ty A′
  dsubstTyOver-sound-raw d dsty-⋆ = refl
  dsubstTyOver-sound-raw d (dsty-hom {A′ = A′} pA pt pu) =
    trans
      (cong (λ B → Raw.[ B ] _ ⇒ _) (dsubstTyOver-sound-raw d pA))
      (cong₂ (λ s1 s2 → Raw.[ Raw-Ty A′ ] s1 ⇒ s2)
             (dsubstTmOver-sound-raw d pt) (dsubstTmOver-sound-raw d pu))

  dsubstTmOver-sound-raw :
    {Γ : Ctx} {D E : DTy Γ} {t : Tm (Γ ▸▸ E)} {t′ : Tm (Γ ▸▸ D)} →
    (d : DTmOverDTy D E) → DSubstTmOver d t t′ →
    Raw-Tm t Raw.[ Raw-Sub (dover-sub d) ]t ≡ Raw-Tm t′
  dsubstTmOver-sound-raw d (dstm-var sv) = dsubstVarOver-sound-raw d sv
  dsubstTmOver-sound-raw d (dstm-coh {A = A} {u = u} {v = v} ss) =
    cong (λ ρ → Raw.coh (Raw-Ty A) (Raw-Tm u) (Raw-Tm v) ρ)
         (dsubstSubOver-sound-raw d ss)

  dsubstSubOver-sound-raw :
    {Γ : Ctx} {D E : DTy Γ} {Δ : Ctx}
    {σ : Sub (Γ ▸▸ E) Δ} {σ′ : Sub (Γ ▸▸ D) Δ} →
    (d : DTmOverDTy D E) → DSubstSubOver d σ σ′ →
    Raw-Sub σ Raw.∘ Raw-Sub (dover-sub d) ≡ Raw-Sub σ′
  dsubstSubOver-sound-raw d dssub-◆ = refl
  dsubstSubOver-sound-raw d (dssub-snoc ss st) =
    cong₂ Raw.⟨_,_⟩ (dsubstSubOver-sound-raw d ss) (dsubstTmOver-sound-raw d st)

  dsubstVarOver-sound-raw :
    {Γ : Ctx} {D E : DTy Γ} {x : Var (Γ ▸▸ E)} {t′ : Tm (Γ ▸▸ D)} →
    (d : DTmOverDTy D E) → DSubstVarOver d x t′ →
    Raw.lookup x (Raw-Sub (dover-sub d)) ≡ Raw-Tm t′
  dsubstVarOver-sound-raw {D = D} ◆ᴰ (dsv-base w) = dwkTm-proj-lookup-raw D w
  dsubstVarOver-sound-raw (d ▸ᴰ a [ p ][ q ]) dsv-zero = refl
  dsubstVarOver-sound-raw (d ▸ᴰ a [ p ][ q ]) (dsv-succ sv) =
    dsubstVarOver-sound-raw d sv
```

The computed action functions are then substitution along `dover-sub d`. They are the
new-style replacement for the old `fill-sub` / `apply-diag-mor-shape` plumbing.

```agda
dsubstTyOver-fun :
  {Γ : Ctx} {D E : DTy Γ} → (d : DTmOverDTy D E) → Ty (Γ ▸▸ E) → Ty (Γ ▸▸ D)
dsubstTyOver-fun d A = A [ dover-sub d ]T

dsubstTmOver-fun :
  {Γ : Ctx} {D E : DTy Γ} → (d : DTmOverDTy D E) → Tm (Γ ▸▸ E) → Tm (Γ ▸▸ D)
dsubstTmOver-fun d t = t [ dover-sub d ]t

dsubstSubOver-fun :
  {Γ : Ctx} {D E : DTy Γ} {Δ : Ctx} →
  (d : DTmOverDTy D E) → Sub (Γ ▸▸ E) Δ → Sub (Γ ▸▸ D) Δ
dsubstSubOver-fun d σ = σ ∘ dover-sub d

dsubstVarOver-fun :
  {Γ : Ctx} {D E : DTy Γ} → (d : DTmOverDTy D E) → Var (Γ ▸▸ E) → Tm (Γ ▸▸ D)
dsubstVarOver-fun d x = lookup x (dover-sub d)
```

Each computed action satisfies the corresponding `DSubst*Over` relation. The soundness
lemmas above record that the raw outputs agree with the relation; the satisfaction
lemmas below package this as relational evidence, which is what diagram-morphism identity
and composition consume. The typed `Ty`/`Tm`/`Sub` *records* offer no eliminator, but
their well-formedness fields `Ty-iswf`/`Tm-iswf`/`Sub-iswf` *are* inductive families, so
the proofs recurse on those (record-eta makes the reconstructed typed sub-pieces
definitionally the originals, and `Ty/Tm/Sub-ext refl` identifies the computed output
with the relation's output). The variable case is self-contained; the substitution case
uses the `sub◆-η` / `subSnoc-inv` inversion lemmas to reconcile the codomain's recorded
type without metavariable ambiguity.

The variable satisfaction lemma is self-contained: it recurses on the section `d`
and the (raw) variable, using `dwkTm-rel` / `dwkTm-proj-lookup-raw` at the ambient
leaf and the definitional `lookup` reductions on the snoc substitution otherwise.

```agda
dsubstVarOver-rel :
  {Γ : Ctx} {D E : DTy Γ} (d : DTmOverDTy D E) (x : Var (Γ ▸▸ E)) →
  DSubstVarOver d x (dsubstVarOver-fun d x)
dsubstVarOver-rel {D = D} ◆ᴰ x =
  subst (DSubstVarOver ◆ᴰ x)
    (sym (Tm-ext (dwkTm-proj-lookup-raw D (dwkTm-rel D (var x)))))
    (dsv-base (dwkTm-rel D (var x)))
dsubstVarOver-rel (d ▸ᴰ a [ p ][ q ]) Raw.zero =
  subst (DSubstVarOver (d ▸ᴰ a [ p ][ q ]) Raw.zero)
    (sym (Tm-ext refl))
    dsv-zero
dsubstVarOver-rel (d ▸ᴰ a [ p ][ q ]) (Raw.succ y) =
  subst (DSubstVarOver (d ▸ᴰ a [ p ][ q ]) (Raw.succ y))
    (sym (Tm-ext refl))
    (dsv-succ (dsubstVarOver-rel d y))
```

Substitutions into `◆` / into a snoc context have the expected shape; these
inversion lemmas isolate the one place where the codomain's recorded type is
reconciled (here it is a rigid parameter, so no metavariable ambiguity arises).

```agda
sub◆-η : {Γ : Ctx} (σ : Sub Γ ◆) → σ ≡ ◆S
sub◆-η (mkSub _ ◆Swf) = refl

subSnoc-inv : {Γ Δ₀ : Ctx} {A : Ty Δ₀} (σ : Sub Γ (Δ₀ ▸ A)) →
  Σ[ σ₀ ∈ Sub Γ Δ₀ ] Σ[ t ∈ Tm Γ ] Σ[ p ∈ HasTySub t A σ₀ ]
    (σ ≡ snocSubEq σ₀ A t p)
subSnoc-inv (mkSub _ (⟨_,_⟩:[_]wf {A = A'} σ₀ t pr)) =
  mkSub (Raw-SubR σ₀) (SubR-wf σ₀)
  , mkTm (Raw-TmR t) (TmR-wf t)
  , pr
  , Sub-ext refl
```

The type/term/substitution satisfaction lemmas are mutually recursive. The typed
records `Ty`/`Tm`/`Sub` have no eliminator, but their well-formedness fields
`Ty-iswf`/`Tm-iswf`/`Sub-iswf` *are* inductive families, so we recurse on those.
Record-eta makes the reconstructed typed sub-pieces (e.g. `mkTy _ (TyR-wf B)`)
definitionally equal to the originals, and the computed output is identified with
the relation's output by `Ty/Tm/Sub-ext refl` (the raw parts already agree).

```agda
mutual
  {-# TERMINATING #-}
  dsubstTyOver-rel :
    {Γ : Ctx} {D E : DTy Γ} (d : DTmOverDTy D E) (A : Ty (Γ ▸▸ E)) →
    DSubstTyOver d A (dsubstTyOver-fun d A)
  dsubstTyOver-rel d (mkTy _ ⋆wf) =
    subst (DSubstTyOver d ⋆) (sym (Ty-ext refl)) dsty-⋆
  dsubstTyOver-rel d (mkTy _ (hom-wf B {u} {v} pu pv)) =
    let B′ = mkTy (Raw-TyR B) (TyR-wf B)
        u′ = mkTm (Raw-TmR u) (TmR-wf u)
        v′ = mkTm (Raw-TmR v) (TmR-wf v)
    in subst (DSubstTyOver d ([ B′ ] u′ ⇒ v′ :[ pu , pv ]))
         (Ty-ext refl)
         (dsty-hom {pt′ = tmSub-typed {t = u′} {A = B′} {σ = dover-sub d} pu}
                   {pu′ = tmSub-typed {t = v′} {A = B′} {σ = dover-sub d} pv}
                   (dsubstTyOver-rel d B′)
                   (dsubstTmOver-rel d u′)
                   (dsubstTmOver-rel d v′))

  dsubstTmOver-rel :
    {Γ : Ctx} {D E : DTy Γ} (d : DTmOverDTy D E) (t : Tm (Γ ▸▸ E)) →
    DSubstTmOver d t (dsubstTmOver-fun d t)
  dsubstTmOver-rel d (mkTm _ (var-wf x)) =
    subst (DSubstTmOver d (var x)) (Tm-ext refl)
      (dstm-var (dsubstVarOver-rel d x))
  dsubstTmOver-rel d (mkTm _ (coh-wf ps wfΔ A u v pu pv fl σ₀)) =
    let A′  = mkTy (Raw-TyR A) (TyR-wf A)
        u′  = mkTm (Raw-TmR u) (TmR-wf u)
        v′  = mkTm (Raw-TmR v) (TmR-wf v)
        σ′  = mkSub (Raw-SubR σ₀) (SubR-wf σ₀)
    in subst (DSubstTmOver d (coh ps A′ u′ v′ pu pv fl σ′))
         (Tm-ext refl)
         (dstm-coh (dsubstSubOver-rel d σ′))

  dsubstSubOver-rel :
    {Γ : Ctx} {D E : DTy Γ} {Δ : Ctx} (d : DTmOverDTy D E) (σ : Sub (Γ ▸▸ E) Δ) →
    DSubstSubOver d σ (dsubstSubOver-fun d σ)
  dsubstSubOver-rel {Δ = mkCtx _ ◆wf} d σ
    rewrite sub◆-η σ =
    subst (DSubstSubOver d ◆S) (sym (Sub-ext refl)) dssub-◆
  dsubstSubOver-rel {Δ = mkCtx _ (wfΘ ▸wf Ac)} d σ
    with subSnoc-inv σ
  ... | σ₀ , t , p , eq
    rewrite eq =
    subst (DSubstSubOver d (snocSubEq σ₀ (mkTy (Raw-TyR Ac) (TyR-wf Ac)) t p))
      (Sub-ext refl)
      (dssub-snoc {pt = p}
                  {pt′ = hasTySub-sub {t = t} {A = mkTy (Raw-TyR Ac) (TyR-wf Ac)}
                                      {τ = σ₀} {σ = dover-sub d} p}
                  (dsubstSubOver-rel d σ₀)
                  (dsubstTmOver-rel d t))
```

## Identity and composition of relative sections

The underlying substitution of a relative section always projects back to the source:
`dty-proj E ∘ dover-sub d ≡ dty-proj D`. This is the relational replacement for the old
`fill-sub-proj` plumbing, proved by structural recursion on the section.

```agda
dover-sub-proj :
  {Γ : Ctx} {D E : DTy Γ} (d : DTmOverDTy D E) →
  dty-proj E ∘ dover-sub d ≡ dty-proj D
dover-sub-proj {D = D} ◆ᴰ = ∘-idS-l (dty-proj D)
dover-sub-proj (_▸ᴰ_[_][_] {D = E₀} {A = A} d a p q) =
  trans
    (sym (∘-assoc (dty-proj E₀) (wk {A = A}) (dover-sub (d ▸ᴰ a [ p ][ q ]))))
    (trans
      (cong (λ σ → dty-proj E₀ ∘ σ) (wk-snoc-sub (dover-sub d)))
      (dover-sub-proj d))
```

**Composition** of relative sections re-bases the second section's entries through the
first, by acting on each head term with `dsubstTmOver-fun`. The entry type evidence is
the action's satisfaction lemma; the head typing is `tmSub-typed`, transported along the
substitution-composition law `dover-sub-comp`. Both are defined mutually.

```agda
mutual
  comp-over :
    {Γ : Ctx} {D E F : DTy Γ} →
    DTmOverDTy D E → DTmOverDTy E F → DTmOverDTy D F
  comp-over φ ◆ᴰ = ◆ᴰ
  comp-over {D = D} {E = E} φ (_▸ᴰ_[_][_] {D = F₀} {A = B} {A′ = B_E} ψ₀ b pb qb) =
    comp-over φ ψ₀ ▸ᴰ dsubstTmOver-fun φ b
      [ dsubstTyOver-rel (comp-over φ ψ₀) B ][ Q ]
    where
      BE-eq : B_E ≡ dsubstTyOver-fun ψ₀ B
      BE-eq = Ty-ext (sym (dsubstTyOver-sound-raw ψ₀ pb))

      eq : dsubstTyOver-fun φ B_E ≡ dsubstTyOver-fun (comp-over φ ψ₀) B
      eq =
        trans (cong (_[ dover-sub φ ]T) BE-eq)
          (trans ([]T-∘ {A = B} {τ = dover-sub ψ₀} {σ = dover-sub φ})
            (cong (λ σ → B [ σ ]T) (sym (dover-sub-comp φ ψ₀))))

      Q : HasTy (dsubstTmOver-fun φ b) (dsubstTyOver-fun (comp-over φ ψ₀) B)
      Q = subst (HasTy (dsubstTmOver-fun φ b)) eq
            (tmSub-typed {t = b} {A = B_E} {σ = dover-sub φ} qb)

  dover-sub-comp :
    {Γ : Ctx} {D E F : DTy Γ} →
    (φ : DTmOverDTy D E) (ψ : DTmOverDTy E F) →
    dover-sub (comp-over φ ψ) ≡ dover-sub ψ ∘ dover-sub φ
  dover-sub-comp φ ◆ᴰ = sym (dover-sub-proj φ)
  dover-sub-comp φ (_▸ᴰ_[_][_] {A = B} {A′ = B_E} ψ₀ b pb qb) =
    Sub-ext (cong₂ Raw.⟨_,_⟩ (cong Raw-Sub (dover-sub-comp φ ψ₀)) refl)
```

**Source weakening** of a section re-bases it across a new source entry `A`, weakening
each head term by `A`. The **identity** section is then built recursively: at `D ▸ᵈ A`
its prefix is the source weakening of the identity on `D`, and its head is the newest
variable. Both come with their `dover-sub` computation (source weakening composes with
`wk`; the identity section's substitution is `idS`), and these are all defined together.

```agda
mutual
  {-# TERMINATING #-}
  srcWkOver-fun :
    {Γ : Ctx} {D E : DTy Γ} →
    (A : Ty (Γ ▸▸ D)) → DTmOverDTy D E → DTmOverDTy (D ▸ᵈ A) E
  srcWkOver-fun A ◆ᴰ = ◆ᴰ
  srcWkOver-fun A (_▸ᴰ_[_][_] {A = B} {A′ = B′} ψ₀ b pb qb) =
    srcWkOver-fun A ψ₀ ▸ᴰ wkTm {A = A} b
      [ dsubstTyOver-rel (srcWkOver-fun A ψ₀) B ][ Q ]
    where
      B′-eq : B′ ≡ dsubstTyOver-fun ψ₀ B
      B′-eq = Ty-ext (sym (dsubstTyOver-sound-raw ψ₀ pb))

      eq : wkTy {A = A} B′ ≡ dsubstTyOver-fun (srcWkOver-fun A ψ₀) B
      eq =
        trans (cong (wkTy {A = A}) B′-eq)
          (trans (wkTy-sub (dsubstTyOver-fun ψ₀ B))
            (trans ([]T-∘ {A = B} {τ = dover-sub ψ₀} {σ = wk {A = A}})
              (cong (λ σ → B [ σ ]T) (sym (dover-sub-srcwk A ψ₀)))))

      Q : HasTy (wkTm {A = A} b) (dsubstTyOver-fun (srcWkOver-fun A ψ₀) B)
      Q = subst (HasTy (wkTm {A = A} b)) eq (hasTy-wk qb)

  dover-sub-srcwk :
    {Γ : Ctx} {D E : DTy Γ} →
    (A : Ty (Γ ▸▸ D)) (d : DTmOverDTy D E) →
    dover-sub (srcWkOver-fun A d) ≡ dover-sub d ∘ wk {A = A}
  dover-sub-srcwk A ◆ᴰ = refl
  dover-sub-srcwk A (_▸ᴰ_[_][_] {A = B} ψ₀ b pb qb) =
    Sub-ext
      (cong₂ Raw.⟨_,_⟩
        (cong Raw-Sub (dover-sub-srcwk A ψ₀))
        (cong Raw-Tm (sym (wkTm-sub {A = A} b))))

  id-over : {Γ : Ctx} (D : DTy Γ) → DTmOverDTy D D
  id-over ◆ᵈ = ◆ᴰ
  id-over (D₀ ▸ᵈ A) =
    srcWkOver-fun A (id-over D₀) ▸ᴰ vz {A = A}
      [ dsubstTyOver-rel (srcWkOver-fun A (id-over D₀)) A ][ Q ]
    where
      wk-eq : dover-sub (srcWkOver-fun A (id-over D₀)) ≡ wk {A = A}
      wk-eq =
        trans (dover-sub-srcwk A (id-over D₀))
          (trans (cong (λ σ → σ ∘ wk {A = A}) (dover-sub-id D₀))
            (∘-idS-l (wk {A = A})))

      eq : wkTy {A = A} A ≡ dsubstTyOver-fun (srcWkOver-fun A (id-over D₀)) A
      eq = trans (wkTy-sub A) (cong (λ σ → A [ σ ]T) (sym wk-eq))

      Q : HasTy (vz {A = A}) (dsubstTyOver-fun (srcWkOver-fun A (id-over D₀)) A)
      Q = subst (HasTy (vz {A = A})) eq (vz-hasTy {A = A})

  dover-sub-id :
    {Γ : Ctx} (D : DTy Γ) → dover-sub (id-over D) ≡ idS (Γ ▸▸ D)
  dover-sub-id ◆ᵈ = refl
  dover-sub-id (D₀ ▸ᵈ A) =
    Sub-ext
      (cong₂ Raw.⟨_,_⟩
        (cong Raw-Sub
          (trans (dover-sub-srcwk A (id-over D₀))
            (trans (cong (λ σ → σ ∘ wk {A = A}) (dover-sub-id D₀))
              (∘-idS-l (wk {A = A})))))
        refl)
```

## Computed substitution of diagram terms

We now realize the relational `SubstDTm` family as a *computed* function:
`substDTm-fun sD d` substitutes the diagram term `d : DTm D` along the context
substitution recognised by `sD : SubstDTy σ D D′ ρ`, producing `d′ : DTm D′`. This is
the `DTm`-level analogue of `dtm-sub` / `dover-sub`, and is what the diagram-hom
substitution `dhom-subst` consumes.

First the *evaluators*: a type / term / substitution / variable of `Γ ▸▸ D` evaluated at a
plain diagram term `d`. These mirror the `dsubst*Over-rel` family, with `dtm-sub d` in
place of `dover-sub d`. They package the canonical computed substitution outputs as the
relational `SubstTyAtDTm` / … witnesses, which the head of `substDTm-fun` needs.

```agda
mutual
  {-# TERMINATING #-}
  substTyAtDTm-rel :
    {Γ : Ctx} {D : DTy Γ} (d : DTm D) (A : Ty (Γ ▸▸ D)) →
    SubstTyAtDTm d A (A [ dtm-sub d ]T)
  substTyAtDTm-rel d (mkTy _ ⋆wf) =
    subst (SubstTyAtDTm d ⋆) (sym (Ty-ext refl)) sty-⋆
  substTyAtDTm-rel d (mkTy _ (hom-wf B {u} {v} pu pv)) =
    let B′ = mkTy (Raw-TyR B) (TyR-wf B)
        u′ = mkTm (Raw-TmR u) (TmR-wf u)
        v′ = mkTm (Raw-TmR v) (TmR-wf v)
    in subst (SubstTyAtDTm d ([ B′ ] u′ ⇒ v′ :[ pu , pv ]))
         (Ty-ext refl)
         (sty-hom {pt′ = tmSub-typed {t = u′} {A = B′} {σ = dtm-sub d} pu}
                  {pu′ = tmSub-typed {t = v′} {A = B′} {σ = dtm-sub d} pv}
                  (substTyAtDTm-rel d B′)
                  (substTmAtDTm-rel d u′)
                  (substTmAtDTm-rel d v′))

  substTmAtDTm-rel :
    {Γ : Ctx} {D : DTy Γ} (d : DTm D) (t : Tm (Γ ▸▸ D)) →
    SubstTmAtDTm d t (t [ dtm-sub d ]t)
  substTmAtDTm-rel d (mkTm _ (var-wf x)) =
    subst (SubstTmAtDTm d (var x)) (Tm-ext refl)
      (stm-var (substVarAtDTm-rel d x))
  substTmAtDTm-rel d (mkTm _ (coh-wf ps wfΔ A u v pu pv fl σ₀)) =
    let A′ = mkTy (Raw-TyR A) (TyR-wf A)
        u′ = mkTm (Raw-TmR u) (TmR-wf u)
        v′ = mkTm (Raw-TmR v) (TmR-wf v)
        σ′ = mkSub (Raw-SubR σ₀) (SubR-wf σ₀)
    in subst (SubstTmAtDTm d (coh ps A′ u′ v′ pu pv fl σ′))
         (Tm-ext refl)
         (stm-coh (substSubAtDTm-rel d σ′))

  substSubAtDTm-rel :
    {Γ : Ctx} {D : DTy Γ} {Δ : Ctx} (d : DTm D) (σ : Sub (Γ ▸▸ D) Δ) →
    SubstSubAtDTm d σ (σ ∘ dtm-sub d)
  substSubAtDTm-rel {Δ = mkCtx _ ◆wf} d σ
    rewrite sub◆-η σ =
    subst (SubstSubAtDTm d ◆S) (sym (Sub-ext refl)) ssub-◆
  substSubAtDTm-rel {Δ = mkCtx _ (wfΘ ▸wf Ac)} d σ
    with subSnoc-inv σ
  ... | σ₀ , t , p , eq
    rewrite eq =
    subst (SubstSubAtDTm d (snocSubEq σ₀ (mkTy (Raw-TyR Ac) (TyR-wf Ac)) t p))
      (Sub-ext refl)
      (ssub-snoc {pt = p}
                 {pt′ = hasTySub-sub {t = t} {A = mkTy (Raw-TyR Ac) (TyR-wf Ac)}
                                     {τ = σ₀} {σ = dtm-sub d} p}
                 (substSubAtDTm-rel d σ₀)
                 (substTmAtDTm-rel d t))

  substVarAtDTm-rel :
    {Γ : Ctx} {D : DTy Γ} (d : DTm D) (x : Var (Γ ▸▸ D)) →
    SubstVarAtDTm d x (lookup x (dtm-sub d))
  substVarAtDTm-rel ◆ᵗ x =
    subst (SubstVarAtDTm ◆ᵗ x) (sym (Tm-ext (Raw.lookup-idS x))) sv-base
  substVarAtDTm-rel (d ▸ᵗ a [ p ][ q ]) Raw.zero =
    subst (SubstVarAtDTm (d ▸ᵗ a [ p ][ q ]) Raw.zero) (sym (Tm-ext refl)) sv-zero
  substVarAtDTm-rel (d ▸ᵗ a [ p ][ q ]) (Raw.succ y) =
    subst (SubstVarAtDTm (d ▸ᵗ a [ p ][ q ]) (Raw.succ y)) (sym (Tm-ext refl))
      (sv-succ (substVarAtDTm-rel d y))
```

`substDTm-fun` is defined mutually with its **section-commutation** lemma
`substDTm-fun-section`, which says the substituted section `dtm-sub (substDTm-fun sD d)`
slots into the lift `ρ` compatibly with `σ`:
`ρ ∘ dtm-sub (substDTm-fun sD d) ≡ dtm-sub d ∘ σ`. The head of `substDTm-fun` needs the
prefix instance of this lemma to retype the substituted entry term.

```agda
mutual
  {-# TERMINATING #-}
  substDTm-fun :
    {Γ Δ : Ctx} {σ : Sub Δ Γ} {D : DTy Γ} {D′ : DTy Δ}
    {ρ : Sub (Δ ▸▸ D′) (Γ ▸▸ D)} →
    SubstDTy σ D D′ ρ → DTm D → DTm D′
  substDTm-fun ◆ˢ ◆ᵗ = ◆ᵗ
  substDTm-fun {σ = σ}
    (_▸ˢ_[_][_] {ρ = ρ₀} {A = A} {A′ = A'} sD₀ w st hp)
    (_▸ᵗ_[_][_] {A′ = Aᵉ} d₀ a pa qa) =
    substDTm-fun sD₀ d₀ ▸ᵗ (a [ σ ]t) [ pa' ][ qa' ]
    where
      d₀′ = substDTm-fun sD₀ d₀
      e : A' [ dtm-sub d₀′ ]T ≡ Aᵉ [ σ ]T
      e = trans (cong (_[ dtm-sub d₀′ ]T) (sym (Ty-ext (Raw.substTy→[]T≡ st))))
          (trans ([]T-∘ {A = A} {τ = ρ₀} {σ = dtm-sub d₀′})
          (trans (cong (λ z → A [ z ]T) (substDTm-fun-section sD₀ d₀))
          (trans (sym ([]T-∘ {A = A} {τ = dtm-sub d₀} {σ = σ}))
                 (cong (_[ σ ]T) (Ty-ext (substTyAtDTm-sound-raw d₀ pa))))))
      pa' : SubstTyAtDTm d₀′ A' (Aᵉ [ σ ]T)
      pa' = subst (SubstTyAtDTm d₀′ A') e (substTyAtDTm-rel d₀′ A')
      qa' : HasTy (a [ σ ]t) (Aᵉ [ σ ]T)
      qa' = tmSub-typed {t = a} {A = Aᵉ} {σ = σ} qa

  substDTm-fun-section :
    {Γ Δ : Ctx} {σ : Sub Δ Γ} {D : DTy Γ} {D′ : DTy Δ}
    {ρ : Sub (Δ ▸▸ D′) (Γ ▸▸ D)} →
    (sD : SubstDTy σ D D′ ρ) (d : DTm D) →
    ρ ∘ dtm-sub (substDTm-fun sD d) ≡ dtm-sub d ∘ σ
  substDTm-fun-section {σ = σ} ◆ˢ ◆ᵗ =
    trans (∘-idS-r σ) (sym (∘-idS-l σ))
  substDTm-fun-section {σ = σ}
    (_▸ˢ_[_][_] {ρ = ρ₀} {A = A} {A′ = A'} sD₀ w st hp)
    (_▸ᵗ_[_][_] {A′ = Aᵉ} d₀ a pa qa) =
    let d₀′ = substDTm-fun sD₀ d₀
        a′  = a [ σ ]t
    in Sub-ext
         (cong₂ Raw.⟨_,_⟩
           (trans
             (cong (λ z → z Raw.∘ Raw.⟨ Raw-Sub (dtm-sub d₀′) , Raw-Tm a′ ⟩)
               (sym (wkSub-unique (Raw.wkSub-rel {A = Raw-Ty A'} (Raw-Sub ρ₀)) w)))
             (trans
               (Raw.wkSub-∘ (Raw-Sub ρ₀) (Raw-Sub (dtm-sub d₀′)) (Raw-Tm a′))
               (cong Raw-Sub (substDTm-fun-section sD₀ d₀))))
           refl)
```

Finally the satisfaction lemma: the computed `substDTm-fun` is recognised by the
relational `SubstDTm`.

```agda
substDTm-rel :
  {Γ Δ : Ctx} {σ : Sub Δ Γ} {D : DTy Γ} {D′ : DTy Δ}
  {ρ : Sub (Δ ▸▸ D′) (Γ ▸▸ D)} →
  (sD : SubstDTy σ D D′ ρ) (d : DTm D) →
  SubstDTm σ sD d (substDTm-fun sD d)
substDTm-rel ◆ˢ ◆ᵗ = ◆ᵗˢ
substDTm-rel {σ = σ}
  (_▸ˢ_[_][_] sD₀ w st hp)
  (_▸ᵗ_[_][_] d₀ a pa qa) =
  _▸ᵗˢ_ (substDTm-rel sD₀ d₀) (Raw.substTm (Raw-Tm a) (Raw-Sub σ))
```

## Base change for relative sections (computed)

The computed representative for `SubstDTmOverDTy`: given relational substitutions
`sD`, `sE` of the source and target diagrams along `σ`, and a relative section
`φ : DTmOverDTy D E`, it produces a base-changed section
`substDTmOverDTy-fun sD sE φ : DTmOverDTy D′ E′`.

Unlike the other `*-fun` representatives in this file, this one is **postulated**.
The snoc case would have to construct, for each head, the base-changed acted-on type
`Aᴰ′` together with the witness `DSubstTyOver φ₀′ A′ Aᴰ′`, and prove the
**base-change/action commutation lemma**

```text
substitution along ρD of (the action of φ₀ on A)
  =  action of φ₀′ on (the substitution of A along ρE)
```

for types, terms, substitutions, and variables. That is exactly the relative-section
analogue of the `SubstTyAtDTm`/`SubstDTy` commutation infrastructure and is large raw
equality plumbing. We therefore postulate the computed representative and its
satisfaction witness here, deferring the commutation lemma to a later pass. The core
relation `SubstDTmOverDTy` is unaffected: it records the compatible outputs
explicitly, so downstream code that only needs *a* base-change (e.g. `Fiber-morphism`)
can use this representative now.

```agda
postulate
  substDTmOverDTy-fun :
    {Γ Δ : Ctx} {σ : Sub Δ Γ}
    {D E : DTy Γ} {D′ E′ : DTy Δ}
    {ρD : Sub (Δ ▸▸ D′) (Γ ▸▸ D)}
    {ρE : Sub (Δ ▸▸ E′) (Γ ▸▸ E)} →
    SubstDTy σ D D′ ρD →
    SubstDTy σ E E′ ρE →
    DTmOverDTy D E →
    DTmOverDTy D′ E′

  substDTmOverDTy-rel :
    {Γ Δ : Ctx} {σ : Sub Δ Γ}
    {D E : DTy Γ} {D′ E′ : DTy Δ}
    {ρD : Sub (Δ ▸▸ D′) (Γ ▸▸ D)}
    {ρE : Sub (Δ ▸▸ E′) (Γ ▸▸ E)} →
    (sD : SubstDTy σ D D′ ρD) →
    (sE : SubstDTy σ E E′ ρE) →
    (φ : DTmOverDTy D E) →
    SubstDTmOverDTy sD sE φ (substDTmOverDTy-fun sD sE φ)
```
