# 4a-Diagrams: diagram types and diagram terms

A **diagram type** over a context `Γ` is a telescope of dependent types
`(A₁, A₂, ⋯, Aₙ)`:

- `◆ᵈ` is the empty diagram type;
- `D ▸ᵈ A` extends a diagram type `D` by a type `A` living over the total context
  of `D`.

The **total context** `Γ ▸▸ D` extends `Γ` by all the entries of `D`.

A **diagram term** of `D` is a tuple `(a₁, a₂, ⋯, aₙ)` where each `aᵢ` is a term of
`Aᵢ` with the earlier entries `(a₁, ⋯, aᵢ₋₁)` plugged in:

- `◆ᵗ` is the unique diagram term of `◆ᵈ`;
- `d ▸ᵗ a` extends a diagram term `d` of `D` by a term `a` of `A` evaluated at `d`.

On top of this the module develops weakening of diagram data along a diagram
projection, substitution of diagram data along a context substitution, and relative
sections of diagram types.

```agda
module 4a-Diagrams where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Nat using (ℕ)

import 1a-RawSyntax as Raw
import 1c-Pasting as Ps
open import 2a-CaTT

infixl 5 _▸ᵈ_ _▸▸_
infixl 6 _▸ᵗ_[_][_]
infixl 6 _▸ᵒ_[_]
infixl 6 _▸ᴰ_[_][_]
```

## Diagram types and diagram terms

The telescope `DTy` and its total context `_▸▸_` are defined by mutual recursion: a
new entry `A` of `D` is a type over the total context `Γ ▸▸ D` built so far.

```agda
mutual
  data DTy (Γ : Ctx) : Set₁ where
    ◆ᵈ    : DTy Γ
    _▸ᵈ_ : (D : DTy Γ) → Ty (Γ ▸▸ D) → DTy Γ

  _▸▸_ : (Γ : Ctx) → DTy Γ → Ctx
  Γ ▸▸ ◆ᵈ = Γ
  Γ ▸▸ (D ▸ᵈ A) = (Γ ▸▸ D) ▸ A
```

A diagram term `DTm D` is a list of terms of `Γ`, one per entry of `D`. 

To state the typing of the next entry, we need to evaluate the entry's type at the
diagram term built so far: the relation `SubstTyAtDTm d A A′` means that plugging 
the entries of `d` into the type `A : Ty (Γ ▸▸ D)` yields `A′ : Ty Γ`. We similarly
need `SubstTmAtDTm`, `SubstVarAtDTm` and `SubstSubAtDTm` for the mutual induction
to work.

```agda
mutual
  data DTm {Γ : Ctx} : DTy Γ → Set₁ where
    ◆ᵗ : DTm ◆ᵈ
    _▸ᵗ_[_][_] :
      {D : DTy Γ} {A : Ty (Γ ▸▸ D)} {A′ : Ty Γ} →
      (d : DTm D) →
      (a : Tm Γ) →
      SubstTyAtDTm d A A′ →
      HasTy a A′ →
      DTm (D ▸ᵈ A)

  -- evaluate a type at a diagram term
  data SubstTyAtDTm {Γ : Ctx} {D : DTy Γ} (d : DTm D) :
      Ty (Γ ▸▸ D) → Ty Γ → Set₁ where
    sty-⋆ : SubstTyAtDTm d ⋆ ⋆
    sty-hom :
      {A : Ty (Γ ▸▸ D)} {A′ : Ty Γ}
      {t u : Tm (Γ ▸▸ D)} {t′ u′ : Tm Γ}
      {pt : HasTy t A} {pu : HasTy u A}
      {pt′ : HasTy t′ A′} {pu′ : HasTy u′ A′} →
      SubstTyAtDTm d A A′ →
      SubstTmAtDTm d t t′ →
      SubstTmAtDTm d u u′ →
      SubstTyAtDTm d ([ A ] t ⇒ u :[ pt , pu ]) ([ A′ ] t′ ⇒ u′ :[ pt′ , pu′ ])

  -- evaluate a term at a diagram term
  data SubstTmAtDTm {Γ : Ctx} {D : DTy Γ} (d : DTm D) :
      Tm (Γ ▸▸ D) → Tm Γ → Set₁ where
    stm-var :
      {x : Var (Γ ▸▸ D)} {t′ : Tm Γ} →
      SubstVarAtDTm d x t′ →
      SubstTmAtDTm d (var x) t′
    stm-coh :
      {Δ : Ctx} {k : ℕ} {ps : Ps.IsPsCtx (Raw-Ctx Δ) k}
      {A : Ty Δ} {u v : Tm Δ}
      {pu : HasTy u A} {pv : HasTy v A}
      {fl : Full ps (Raw-Ty A) (Raw-Tm u) (Raw-Tm v)}
      {σ : Sub (Γ ▸▸ D) Δ} {σ′ : Sub Γ Δ} →
      SubstSubAtDTm d σ σ′ →
      SubstTmAtDTm d (coh ps A u v pu pv fl σ) (coh ps A u v pu pv fl σ′)

  -- evaluate a substitution at a diagram term
  data SubstSubAtDTm {Γ : Ctx} {D : DTy Γ} (d : DTm D) :
      {Δ : Ctx} → Sub (Γ ▸▸ D) Δ → Sub Γ Δ → Set₁ where
    ssub-◆ : SubstSubAtDTm d ◆S ◆S
    ssub-snoc :
      {Δ : Ctx} {A : Ty Δ}
      {σ₀ : Sub (Γ ▸▸ D) Δ} {σ₀′ : Sub Γ Δ}
      {t : Tm (Γ ▸▸ D)} {t′ : Tm Γ}
      {pt : HasTySub t A σ₀} {pt′ : HasTySub t′ A σ₀′} →
      SubstSubAtDTm d σ₀ σ₀′ →
      SubstTmAtDTm d t t′ →
      SubstSubAtDTm d (snocSubEq σ₀ A t pt) (snocSubEq σ₀′ A t′ pt′)

  -- where a variable goes when evaluated at a diagram term
  data SubstVarAtDTm {Γ : Ctx} :
      {D : DTy Γ} → DTm D → Var (Γ ▸▸ D) → Tm Γ → Set₁ where
    -- ambient variable: stays itself
    sv-base :
      {x : Var Γ} →
      SubstVarAtDTm ◆ᵗ x (var x)
    -- top diagram variable: the stored entry
    sv-zero :
      {D : DTy Γ} {A : Ty (Γ ▸▸ D)} {A′ : Ty Γ}
      {d : DTm D} {a : Tm Γ}
      {p : SubstTyAtDTm d A A′} {q : HasTy a A′} →
      SubstVarAtDTm (d ▸ᵗ a [ p ][ q ]) (zero {A = A}) a
    -- earlier diagram variable: recurse into the prefix
    sv-succ :
      {D : DTy Γ} {A : Ty (Γ ▸▸ D)} {A′ : Ty Γ}
      {d : DTm D} {a : Tm Γ}
      {p : SubstTyAtDTm d A A′} {q : HasTy a A′}
      {y : Var (Γ ▸▸ D)} {t′ : Tm Γ} →
      SubstVarAtDTm d y t′ →
      SubstVarAtDTm (d ▸ᵗ a [ p ][ q ]) (succ {A = A} y) t′
```

## Weakening along a diagram projection

The weakening relation `DWkTy D B B′` records that `B′ : Ty (Γ ▸▸ D)` is the 
weakening of `B : Ty Γ` along the projection `Γ ▸▸ D → Γ`; `DWkTm` and `DWkSub` 
are the analogues for terms and for the domain of a substitution. They are the 
diagram analogue of the raw single-step weakenings `Raw.WkTy`/`Raw.WkTm`/`Raw.WkSub`. 

In each case:

- weakening along the empty diagram is the identity;
- weakening along `D ▸ᵈ A` is weakening along `D` followed by one raw step across `A`.

```agda
data DWkTy {Γ : Ctx} : (D : DTy Γ) → Ty Γ → Ty (Γ ▸▸ D) → Set₁ where
  dwkTy-◆ : {B : Ty Γ} → DWkTy ◆ᵈ B B
  dwkTy-▸ :
    {D : DTy Γ} {A : Ty (Γ ▸▸ D)} {B : Ty Γ}
    {B′ : Ty (Γ ▸▸ D)} {B″ : Ty ((Γ ▸▸ D) ▸ A)} →
    DWkTy D B B′ →
    Raw.WkTy (Raw-Ty B′) (Raw-Ty B″) →
    DWkTy (D ▸ᵈ A) B B″

data DWkTm {Γ : Ctx} : (D : DTy Γ) → Tm Γ → Tm (Γ ▸▸ D) → Set₁ where
  dwkTm-◆ : {t : Tm Γ} → DWkTm ◆ᵈ t t
  dwkTm-▸ :
    {D : DTy Γ} {A : Ty (Γ ▸▸ D)} {t : Tm Γ}
    {t′ : Tm (Γ ▸▸ D)} {t″ : Tm ((Γ ▸▸ D) ▸ A)} →
    DWkTm D t t′ →
    Raw.WkTm (Raw-Tm t′) (Raw-Tm t″) →
    DWkTm (D ▸ᵈ A) t t″

data DWkSub {Γ Δ : Ctx} : (D : DTy Γ) → Sub Γ Δ → Sub (Γ ▸▸ D) Δ → Set₁ where
  dwkSub-◆ : {σ : Sub Γ Δ} → DWkSub ◆ᵈ σ σ
  dwkSub-▸ :
    {D : DTy Γ} {A : Ty (Γ ▸▸ D)} {σ : Sub Γ Δ}
    {σ′ : Sub (Γ ▸▸ D) Δ} {σ″ : Sub ((Γ ▸▸ D) ▸ A) Δ} →
    DWkSub D σ σ′ →
    Raw.WkSub (Raw-Sub σ′) (Raw-Sub σ″) →
    DWkSub (D ▸ᵈ A) σ σ″
```

We can weaken whole *diagram* types and terms along a diagram projection as well.
`DWkDTy D E E′` records that `E′ : DTy (Γ ▸▸ D)` is the weakening of `E : DTy Γ`
along `Γ ▸▸ D → Γ`. 

Each entry of `E` lives over `Γ ▸▸ E₀` for an earlier prefix `E₀`, so weakening it 
inserts the entries of `D` *underneath* that prefix. This lifted weakening of a 
single type/term/substitution is recognized by `LiftWkTy`/`LiftWkTm`/`LiftWkSub`, 
whose variable leaf `LiftWkVar` sends an ambient variable to its `DWkTm`-weakening 
and a prefix variable to the corresponding prefix variable.

```agda
mutual
  data DWkDTy {Γ : Ctx} (D : DTy Γ) : (E : DTy Γ) → DTy (Γ ▸▸ D) → Set₁ where
    dwkD-◆ : DWkDTy D ◆ᵈ ◆ᵈ
    dwkD-▸ :
      {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)}
      {A : Ty (Γ ▸▸ E)} {A′ : Ty ((Γ ▸▸ D) ▸▸ E′)} →
      (w : DWkDTy D E E′) →
      LiftWkTy D w A A′ →
      DWkDTy D (E ▸ᵈ A) (E′ ▸ᵈ A′)

  data LiftWkTy {Γ : Ctx} (D : DTy Γ) :
      {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)} → DWkDTy D E E′ →
      Ty (Γ ▸▸ E) → Ty ((Γ ▸▸ D) ▸▸ E′) → Set₁ where
    lwty-⋆ :
      {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)} {w : DWkDTy D E E′} →
      LiftWkTy D w ⋆ ⋆
    lwty-hom :
      {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)} {w : DWkDTy D E E′}
      {A : Ty (Γ ▸▸ E)} {A′ : Ty ((Γ ▸▸ D) ▸▸ E′)}
      {t u : Tm (Γ ▸▸ E)} {t′ u′ : Tm ((Γ ▸▸ D) ▸▸ E′)}
      {pt : HasTy t A} {pu : HasTy u A}
      {pt′ : HasTy t′ A′} {pu′ : HasTy u′ A′} →
      LiftWkTy D w A A′ →
      LiftWkTm D w t t′ →
      LiftWkTm D w u u′ →
      LiftWkTy D w ([ A ] t ⇒ u :[ pt , pu ]) ([ A′ ] t′ ⇒ u′ :[ pt′ , pu′ ])

  data LiftWkTm {Γ : Ctx} (D : DTy Γ) :
      {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)} → DWkDTy D E E′ →
      Tm (Γ ▸▸ E) → Tm ((Γ ▸▸ D) ▸▸ E′) → Set₁ where
    lwtm-var :
      {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)} {w : DWkDTy D E E′}
      {x : Var (Γ ▸▸ E)} {t′ : Tm ((Γ ▸▸ D) ▸▸ E′)} →
      LiftWkVar D w x t′ →
      LiftWkTm D w (var x) t′
    lwtm-coh :
      {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)} {w : DWkDTy D E E′}
      {Δ : Ctx} {k : ℕ} {ps : Ps.IsPsCtx (Raw-Ctx Δ) k}
      {A : Ty Δ} {u v : Tm Δ}
      {pu : HasTy u A} {pv : HasTy v A}
      {fl : Full ps (Raw-Ty A) (Raw-Tm u) (Raw-Tm v)}
      {σ : Sub (Γ ▸▸ E) Δ} {σ′ : Sub ((Γ ▸▸ D) ▸▸ E′) Δ} →
      LiftWkSub D w σ σ′ →
      LiftWkTm D w (coh ps A u v pu pv fl σ) (coh ps A u v pu pv fl σ′)

  data LiftWkSub {Γ : Ctx} (D : DTy Γ) :
      {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)} → DWkDTy D E E′ →
      {Θ : Ctx} → Sub (Γ ▸▸ E) Θ → Sub ((Γ ▸▸ D) ▸▸ E′) Θ → Set₁ where
    lwsub-◆ :
      {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)} {w : DWkDTy D E E′} →
      LiftWkSub D w ◆S ◆S
    lwsub-snoc :
      {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)} {w : DWkDTy D E E′}
      {Θ : Ctx} {B : Ty Θ}
      {σ₀ : Sub (Γ ▸▸ E) Θ} {σ₀′ : Sub ((Γ ▸▸ D) ▸▸ E′) Θ}
      {t : Tm (Γ ▸▸ E)} {t′ : Tm ((Γ ▸▸ D) ▸▸ E′)}
      {pt : HasTySub t B σ₀} {pt′ : HasTySub t′ B σ₀′} →
      LiftWkSub D w σ₀ σ₀′ →
      LiftWkTm D w t t′ →
      LiftWkSub D w (snocSubEq σ₀ B t pt) (snocSubEq σ₀′ B t′ pt′)

  data LiftWkVar {Γ : Ctx} (D : DTy Γ) :
      {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)} → DWkDTy D E E′ →
      Var (Γ ▸▸ E) → Tm ((Γ ▸▸ D) ▸▸ E′) → Set₁ where
    lwv-base :
      {x : Var Γ} {t′ : Tm (Γ ▸▸ D)} →
      DWkTm D (var x) t′ →
      LiftWkVar D dwkD-◆ x t′
    lwv-zero :
      {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)} {w : DWkDTy D E E′}
      {B : Ty (Γ ▸▸ E)} {B′ : Ty ((Γ ▸▸ D) ▸▸ E′)}
      {lw : LiftWkTy D w B B′} →
      LiftWkVar D (dwkD-▸ w lw) (zero {A = B}) (vz {A = B′})
    lwv-succ :
      {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)} {w : DWkDTy D E E′}
      {B : Ty (Γ ▸▸ E)} {B′ : Ty ((Γ ▸▸ D) ▸▸ E′)}
      {lw : LiftWkTy D w B B′}
      {y : Var (Γ ▸▸ E)} {t′ : Tm ((Γ ▸▸ D) ▸▸ E′)}
      {t″ : Tm (((Γ ▸▸ D) ▸▸ E′) ▸ B′)} →
      LiftWkVar D w y t′ →
      Raw.WkTm (Raw-Tm t′) (Raw-Tm t″) →
      LiftWkVar D (dwkD-▸ w lw) (succ {A = B} y) t″
```

`DWkDTm D w d d′` weakens a diagram term `d : DTm E` (entries over `Γ`) to
`d′ : DTm E′` (entries over `Γ ▸▸ D`), each entry related by `DWkTm`.

```agda
data DWkDTm {Γ : Ctx} (D : DTy Γ) :
    {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)} → DWkDTy D E E′ → DTm E → DTm E′ → Set₁ where
  dwkDt-◆ : DWkDTm D dwkD-◆ ◆ᵗ ◆ᵗ
  dwkDt-▸ :
    {E : DTy Γ} {E′ : DTy (Γ ▸▸ D)} {w : DWkDTy D E E′}
    {A : Ty (Γ ▸▸ E)} {A′ : Ty ((Γ ▸▸ D) ▸▸ E′)} {lw : LiftWkTy D w A A′}
    {d : DTm E} {d′ : DTm E′}
    {a : Tm Γ} {a′ : Tm (Γ ▸▸ D)}
    {Aᵉ : Ty Γ} {Aᵉ′ : Ty (Γ ▸▸ D)}
    {pa : SubstTyAtDTm d A Aᵉ} {qa : HasTy a Aᵉ}
    {pa′ : SubstTyAtDTm d′ A′ Aᵉ′} {qa′ : HasTy a′ Aᵉ′} →
    DWkDTm D w d d′ →
    DWkTm D a a′ →
    DWkDTm D (dwkD-▸ w lw) (d ▸ᵗ a [ pa ][ qa ]) (d′ ▸ᵗ a′ [ pa′ ][ qa′ ])
```

## Substitution along a context substitution

`SubstDTy σ D D′ ρ` means: substituting the diagram type `D` (over `Γ`) along
`σ : Δ → Γ` yields the diagram type `D′` (over `Δ`), with the **lifted total
substitution** `ρ : Δ ▸▸ D′ → Γ ▸▸ D` carried as an index. The snoc step keeps
everything relational: `ρwk` is a `Raw.WkSub` of `ρ` across the new entry `A′`
(never `ρ ∘ wk`), the head type is related by `Raw.SubstTy` (never `A [ ρ ]T`), and
the head typing is supplied as `HasTySub`.

```agda
data SubstDTy {Γ Δ : Ctx} (σ : Sub Δ Γ) :
    (D : DTy Γ) → (D′ : DTy Δ) → Sub (Δ ▸▸ D′) (Γ ▸▸ D) → Set₁ where
  ◆ˢ : SubstDTy σ ◆ᵈ ◆ᵈ σ

  _▸ˢ_[_][_] :
    {D : DTy Γ} {D′ : DTy Δ} {ρ : Sub (Δ ▸▸ D′) (Γ ▸▸ D)}
    {A : Ty (Γ ▸▸ D)} {A′ : Ty (Δ ▸▸ D′)}
    {ρwk : Sub ((Δ ▸▸ D′) ▸ A′) (Γ ▸▸ D)} →
    SubstDTy σ D D′ ρ →
    Raw.WkSub (Raw-Sub ρ) (Raw-Sub ρwk) →
    Raw.SubstTy (Raw-Ty A) (Raw-Sub ρ) (Raw-Ty A′) →
    (p : HasTySub (vz {A = A′}) A ρwk) →
    SubstDTy σ (D ▸ᵈ A) (D′ ▸ᵈ A′)
      (⟨ ρwk , vz {A = A′} ⟩:[ p ])
```

`SubstDTm σ s d d′` substitutes a diagram term: `d : DTm D` over `Γ` becomes
`d′ : DTm D′` over `Δ`, where `s : SubstDTy σ D D′ ρ` substitutes the underlying
diagram type. Each entry `a : Tm Γ` is related to its image `a′ : Tm Δ` by
`Raw.SubstTm` (never `a [ σ ]t`).

```agda
data SubstDTm {Γ Δ : Ctx} (σ : Sub Δ Γ) :
    {D : DTy Γ} {D′ : DTy Δ} {ρ : Sub (Δ ▸▸ D′) (Γ ▸▸ D)} →
    SubstDTy σ D D′ ρ → DTm D → DTm D′ → Set₁ where
  ◆ᵗˢ : SubstDTm σ ◆ˢ ◆ᵗ ◆ᵗ

  _▸ᵗˢ_ :
    {D : DTy Γ} {D′ : DTy Δ} {ρ : Sub (Δ ▸▸ D′) (Γ ▸▸ D)}
    {A : Ty (Γ ▸▸ D)} {A′ : Ty (Δ ▸▸ D′)}
    {ρwk : Sub ((Δ ▸▸ D′) ▸ A′) (Γ ▸▸ D)}
    {s : SubstDTy σ D D′ ρ}
    {w : Raw.WkSub (Raw-Sub ρ) (Raw-Sub ρwk)}
    {st : Raw.SubstTy (Raw-Ty A) (Raw-Sub ρ) (Raw-Ty A′)}
    {hp : HasTySub (vz {A = A′}) A ρwk}
    {d : DTm D} {d′ : DTm D′}
    {a : Tm Γ} {a′ : Tm Δ}
    {Aᵉ : Ty Γ} {Aᵉ′ : Ty Δ}
    {pa : SubstTyAtDTm d A Aᵉ} {qa : HasTy a Aᵉ}
    {pa′ : SubstTyAtDTm d′ A′ Aᵉ′} {qa′ : HasTy a′ Aᵉ′} →
    SubstDTm σ s d d′ →
    Raw.SubstTm (Raw-Tm a) (Raw-Sub σ) (Raw-Tm a′) →
    SubstDTm σ
      (_▸ˢ_[_][_] {A = A} {A′ = A′} {ρwk = ρwk} s w st hp)
      (d ▸ᵗ a [ pa ][ qa ]) (d′ ▸ᵗ a′ [ pa′ ][ qa′ ])
```

## Relative sections

A section `DTmOverSub σ D` over a *given* base substitution `σ : Sub Δ Γ` produces an
underlying substitution `dtmOverSub-sub : Sub Δ (Γ ▸▸ D)`, so it remains a function.
The head typing premise is the relational `HasTySub`.

```agda
mutual
  data DTmOverSub {Γ Δ : Ctx} (σ : Sub Δ Γ) : DTy Γ → Set₁ where
    ◆ᵒ : DTmOverSub σ ◆ᵈ

    _▸ᵒ_[_] :
      {D : DTy Γ} {A : Ty (Γ ▸▸ D)} →
      (d : DTmOverSub σ D) →
      (a : Tm Δ) →
      HasTySub a A (dtmOverSub-sub d) →
      DTmOverSub σ (D ▸ᵈ A)

  dtmOverSub-sub :
    {Γ Δ : Ctx} {σ : Sub Δ Γ} {D : DTy Γ} →
    DTmOverSub σ D → Sub Δ (Γ ▸▸ D)
  dtmOverSub-sub {σ = σ} ◆ᵒ = σ
  dtmOverSub-sub (d ▸ᵒ a [ p ]) = ⟨ dtmOverSub-sub d , a ⟩:[ p ]
```

A section `DTmOverDTy D′ D` is a section of `D` over the diagram context `Γ ▸▸ D′`: a
list of terms in `Γ ▸▸ D′`, one per entry of `D`, where the next entry's type is the
action of the section-so-far on the corresponding entry of `D`. As in
`SubstTyAtDTm`, the action is recognized structurally, with the variable leaf
`DSubstVarOver` sending an ambient variable to its weakening along `D′` (via `DWkTm`)
and a diagram variable to the stored component.

```agda
mutual
  data DTmOverDTy {Γ : Ctx} (D′ : DTy Γ) : DTy Γ → Set₁ where
    ◆ᴰ : DTmOverDTy D′ ◆ᵈ
    _▸ᴰ_[_][_] :
      {D : DTy Γ} {A : Ty (Γ ▸▸ D)} {A′ : Ty (Γ ▸▸ D′)} →
      (d : DTmOverDTy D′ D) →
      (a : Tm (Γ ▸▸ D′)) →
      DSubstTyOver d A A′ →
      HasTy a A′ →
      DTmOverDTy D′ (D ▸ᵈ A)

  data DSubstTyOver {Γ : Ctx} {D′ D : DTy Γ} (d : DTmOverDTy D′ D) :
      Ty (Γ ▸▸ D) → Ty (Γ ▸▸ D′) → Set₁ where
    dsty-⋆ : DSubstTyOver d ⋆ ⋆
    dsty-hom :
      {A : Ty (Γ ▸▸ D)} {A′ : Ty (Γ ▸▸ D′)}
      {t u : Tm (Γ ▸▸ D)} {t′ u′ : Tm (Γ ▸▸ D′)}
      {pt : HasTy t A} {pu : HasTy u A}
      {pt′ : HasTy t′ A′} {pu′ : HasTy u′ A′} →
      DSubstTyOver d A A′ →
      DSubstTmOver d t t′ →
      DSubstTmOver d u u′ →
      DSubstTyOver d ([ A ] t ⇒ u :[ pt , pu ]) ([ A′ ] t′ ⇒ u′ :[ pt′ , pu′ ])

  data DSubstTmOver {Γ : Ctx} {D′ D : DTy Γ} (d : DTmOverDTy D′ D) :
      Tm (Γ ▸▸ D) → Tm (Γ ▸▸ D′) → Set₁ where
    dstm-var :
      {x : Var (Γ ▸▸ D)} {t′ : Tm (Γ ▸▸ D′)} →
      DSubstVarOver d x t′ →
      DSubstTmOver d (var x) t′
    dstm-coh :
      {Δ : Ctx} {k : ℕ} {ps : Ps.IsPsCtx (Raw-Ctx Δ) k}
      {A : Ty Δ} {u v : Tm Δ}
      {pu : HasTy u A} {pv : HasTy v A}
      {fl : Full ps (Raw-Ty A) (Raw-Tm u) (Raw-Tm v)}
      {σ : Sub (Γ ▸▸ D) Δ} {σ′ : Sub (Γ ▸▸ D′) Δ} →
      DSubstSubOver d σ σ′ →
      DSubstTmOver d (coh ps A u v pu pv fl σ) (coh ps A u v pu pv fl σ′)

  data DSubstSubOver {Γ : Ctx} {D′ D : DTy Γ} (d : DTmOverDTy D′ D) :
      {Δ : Ctx} → Sub (Γ ▸▸ D) Δ → Sub (Γ ▸▸ D′) Δ → Set₁ where
    dssub-◆ : DSubstSubOver d ◆S ◆S
    dssub-snoc :
      {Δ : Ctx} {A : Ty Δ}
      {σ₀ : Sub (Γ ▸▸ D) Δ} {σ₀′ : Sub (Γ ▸▸ D′) Δ}
      {t : Tm (Γ ▸▸ D)} {t′ : Tm (Γ ▸▸ D′)}
      {pt : HasTySub t A σ₀} {pt′ : HasTySub t′ A σ₀′} →
      DSubstSubOver d σ₀ σ₀′ →
      DSubstTmOver d t t′ →
      DSubstSubOver d (snocSubEq σ₀ A t pt) (snocSubEq σ₀′ A t′ pt′)

  data DSubstVarOver {Γ : Ctx} {D′ : DTy Γ} :
      {D : DTy Γ} → DTmOverDTy D′ D → Var (Γ ▸▸ D) → Tm (Γ ▸▸ D′) → Set₁ where
    dsv-base :
      {x : Var Γ} {t′ : Tm (Γ ▸▸ D′)} →
      DWkTm D′ (var x) t′ →
      DSubstVarOver ◆ᴰ x t′
    dsv-zero :
      {D : DTy Γ} {A : Ty (Γ ▸▸ D)} {A′ : Ty (Γ ▸▸ D′)}
      {d : DTmOverDTy D′ D} {a : Tm (Γ ▸▸ D′)}
      {p : DSubstTyOver d A A′} {q : HasTy a A′} →
      DSubstVarOver (d ▸ᴰ a [ p ][ q ]) (zero {A = A}) a
    dsv-succ :
      {D : DTy Γ} {A : Ty (Γ ▸▸ D)} {A′ : Ty (Γ ▸▸ D′)}
      {d : DTmOverDTy D′ D} {a : Tm (Γ ▸▸ D′)}
      {p : DSubstTyOver d A A′} {q : HasTy a A′}
      {y : Var (Γ ▸▸ D)} {t′ : Tm (Γ ▸▸ D′)} →
      DSubstVarOver d y t′ →
      DSubstVarOver (d ▸ᴰ a [ p ][ q ]) (succ {A = A} y) t′
```

**Remark (redundancy with `SubstTyAtDTm`).** A diagram term `DTm D` is exactly the
`D′ = ◆ᵈ` case of `DTmOverDTy`, and correspondingly `SubstTyAtDTm`/`SubstTmAtDTm`/
`SubstSubAtDTm` are the `D′ = ◆ᵈ` cases of `DSubstTyOver`/`DSubstTmOver`/
`DSubstSubOver` (the variable leaf's ambient case `DWkTm ◆ᵈ` is the identity). We keep
`DTm` and its evaluation as a separate, direct definition because reading a diagram
term as a plain list of terms of `Γ` — rather than a section over the empty diagram —
is clearer. If translating between the two families ever becomes both necessary and
annoying, they can be unified.

`SubstDTmOverSub τ c d e` reindexes a section over `σ` along `τ` to a section over
`υ`, where `c : CompSub (Raw-Sub σ) (Raw-Sub τ) (Raw-Sub υ)` witnesses `σ ∘ τ = υ`
raw. Its only structural law `substDTmOverSub-sub` is relational composition
evidence.

```agda
data SubstDTmOverSub
  {Γ Δ Θ : Ctx} {σ : Sub Δ Γ} {υ : Sub Θ Γ}
  (τ : Sub Θ Δ)
  (c : Raw.CompSub (Raw-Sub σ) (Raw-Sub τ) (Raw-Sub υ))
  : {D : DTy Γ} → DTmOverSub σ D → DTmOverSub υ D → Set₁ where

  ◆ᵒˢ : SubstDTmOverSub τ c ◆ᵒ ◆ᵒ

  _▸ᵒˢ_ :
    {D : DTy Γ} {A : Ty (Γ ▸▸ D)}
    {d : DTmOverSub σ D} {e : DTmOverSub υ D}
    {a : Tm Δ} {a′ : Tm Θ}
    {pa : HasTySub a A (dtmOverSub-sub d)}
    {pa′ : HasTySub a′ A (dtmOverSub-sub e)} →
    SubstDTmOverSub τ c d e →
    Raw.SubstTm (Raw-Tm a) (Raw-Sub τ) (Raw-Tm a′) →
    SubstDTmOverSub τ c
      (_▸ᵒ_[_] {D = D} {A = A} d a pa)
      (_▸ᵒ_[_] {D = D} {A = A} e a′ pa′)

substDTmOverSub-sub :
  {Γ Δ Θ : Ctx} {σ : Sub Δ Γ} {υ : Sub Θ Γ} {D : DTy Γ}
  (τ : Sub Θ Δ)
  {c : Raw.CompSub (Raw-Sub σ) (Raw-Sub τ) (Raw-Sub υ)}
  {d : DTmOverSub σ D} {e : DTmOverSub υ D} →
  SubstDTmOverSub τ c d e →
  Raw.CompSub
    (Raw-Sub (dtmOverSub-sub d))
    (Raw-Sub τ)
    (Raw-Sub (dtmOverSub-sub e))
substDTmOverSub-sub τ {c = c} ◆ᵒˢ = c
substDTmOverSub-sub τ (s ▸ᵒˢ stm) =
  Raw.comp-snoc (substDTmOverSub-sub τ s) stm
```

## Base change for relative sections

A relative section `φ : DTmOverDTy D E` (a section of the *target* diagram `E` over
the *source* diagram context `Γ ▸▸ D`) can be reindexed along a base substitution
`σ : Sub Δ Γ`, provided we already have relational substitutions of **both** the
source and the target diagram along `σ`. `SubstDTmOverDTy sD sE φ φ′` recognizes a
section `φ′ : DTmOverDTy D′ E′` over `Δ` as the base-change of `φ`.

The recursion runs over the **target** substitution `sE`. The base case sends the
empty section to the empty section. The snoc case extends a recognized base-change
`φ₀ ↦ φ₀′` by a new head: the new source term `a′` is the substitution of the old
head `a` along the source total substitution `ρD` (relationally, `Raw.SubstTm` along
`ρD`).

**Key commutation principle.** The snoc case must relate the base-change of the
acted-on head type to the action of the base-changed section. The old head type
`Aᴰ` is the action of `φ₀` on the target entry `A`; the new head type `Aᴰ′` should
be the action of `φ₀′` on the base-changed entry `A′`. Rather than *prove* that
substituting `Aᴰ` along `ρD` computes to `Aᴰ′` — the base-change/action commutation
lemma — the relation **records the compatible output explicitly**: the witness
`p′ : DSubstTyOver φ₀′ A′ Aᴰ′` (and `q′ : HasTy a′ Aᴰ′`) are supplied as part of the
recognized section `φ₀′ ▸ᴰ a′ [ p′ ][ q′ ]`. So the core recognizes a base-changed
section; it does not compute one. The computational companion may later choose
canonical outputs.

```agda
data SubstDTmOverDTy
  {Γ Δ : Ctx} {σ : Sub Δ Γ}
  {D : DTy Γ} {D′ : DTy Δ} {ρD : Sub (Δ ▸▸ D′) (Γ ▸▸ D)}
  (sD : SubstDTy σ D D′ ρD) :
  {E : DTy Γ} {E′ : DTy Δ} {ρE : Sub (Δ ▸▸ E′) (Γ ▸▸ E)} →
  SubstDTy σ E E′ ρE →
  DTmOverDTy D E →
  DTmOverDTy D′ E′ →
  Set₁ where

  ◆ᴰˢ : SubstDTmOverDTy sD ◆ˢ ◆ᴰ ◆ᴰ

  _▸ᴰˢ_ :
    {E : DTy Γ} {E′ : DTy Δ} {ρE : Sub (Δ ▸▸ E′) (Γ ▸▸ E)}
    {A : Ty (Γ ▸▸ E)} {A′ : Ty (Δ ▸▸ E′)}
    {ρEwk : Sub ((Δ ▸▸ E′) ▸ A′) (Γ ▸▸ E)}
    {sE : SubstDTy σ E E′ ρE}
    {wE : Raw.WkSub (Raw-Sub ρE) (Raw-Sub ρEwk)}
    {stE : Raw.SubstTy (Raw-Ty A) (Raw-Sub ρE) (Raw-Ty A′)}
    {pE : HasTySub (vz {A = A′}) A ρEwk}
    {φ₀ : DTmOverDTy D E} {φ₀′ : DTmOverDTy D′ E′}
    {a : Tm (Γ ▸▸ D)} {a′ : Tm (Δ ▸▸ D′)}
    {Aᴰ : Ty (Γ ▸▸ D)} {Aᴰ′ : Ty (Δ ▸▸ D′)}
    {p : DSubstTyOver φ₀ A Aᴰ} {q : HasTy a Aᴰ}
    {p′ : DSubstTyOver φ₀′ A′ Aᴰ′} {q′ : HasTy a′ Aᴰ′} →
    SubstDTmOverDTy sD sE φ₀ φ₀′ →
    Raw.SubstTm (Raw-Tm a) (Raw-Sub ρD) (Raw-Tm a′) →
    SubstDTmOverDTy sD
      (_▸ˢ_[_][_] {A = A} {A′ = A′} {ρwk = ρEwk} sE wE stE pE)
      (φ₀ ▸ᴰ a [ p ][ q ])
      (φ₀′ ▸ᴰ a′ [ p′ ][ q′ ])
```

## Generic entry helpers

An **entry** of a diagram type `D` picks out one of its components. This is pure
combinatorics — a position in the telescope — so it is a plain inductive type, with no
relational subtlety:

```agda
data Entry {Γ : Ctx} : DTy Γ → Set₁ where
  here  : {D : DTy Γ} {A : Ty (Γ ▸▸ D)} → Entry (D ▸ᵈ A)
  there : {D : DTy Γ} {A : Ty (Γ ▸▸ D)} → Entry D → Entry (D ▸ᵈ A)
```

### Reindexing entries along a diagram substitution

Reindexing a diagram type does not change the combinatorial positions of its entries.
In the computational setting this was phrased against `D [ σ ]dT`; here, where the
substituted diagram `D′` is recognized relationally by `SubstDTy σ D D′ ρ`, we recurse
on that witness instead. Both directions are pure position-shuffling:

```agda
-- Entries of D transport to entries of its substitution D′.
entry-reindex :
  {Γ Δ : Ctx} {σ : Sub Δ Γ} {D : DTy Γ} {D′ : DTy Δ}
  {ρ : Sub (Δ ▸▸ D′) (Γ ▸▸ D)} →
  SubstDTy σ D D′ ρ → Entry D → Entry D′
entry-reindex ◆ˢ ()
entry-reindex (s ▸ˢ _ [ _ ][ _ ]) here      = here
entry-reindex (s ▸ˢ _ [ _ ][ _ ]) (there e) = there (entry-reindex s e)

-- The inverse combinatorial operation.
entry-unreindex :
  {Γ Δ : Ctx} {σ : Sub Δ Γ} {D : DTy Γ} {D′ : DTy Δ}
  {ρ : Sub (Δ ▸▸ D′) (Γ ▸▸ D)} →
  SubstDTy σ D D′ ρ → Entry D′ → Entry D
entry-unreindex ◆ˢ ()
entry-unreindex (s ▸ˢ _ [ _ ][ _ ]) here      = here
entry-unreindex (s ▸ˢ _ [ _ ][ _ ]) (there e) = there (entry-unreindex s e)
```

## Bundled entry data

For a chosen entry `e : Entry D` we extract the basic entrywise combinatorics:

- `D-prefix e` is the prefix diagram before the chosen entry,
- `A-ty e` is the type stored at that entry (living over `Γ ▸▸ D-prefix e`),
- `prefix-in e` embeds entries of the prefix `D-prefix e` back into the full telescope.

These three are exactly the components of the old bundle that remain definable in the
relational core: they are pure combinatorics plus the stored type. The fourth component
of the old `EntryData`, the projection `project-prefix : Sub (Γ ▸▸ D) (Γ ▸▸ prefix)`
(and the derived `prefix-proj`), is **omitted**: it is built from computed weakening
`wk` and composition `_∘_`, which live in the computational companion, not here. It
would need a relational reformulation (a `DWkSub`-style projection witness) before it
could return.

The remaining three return types are coupled — `A-ty`'s and `prefix-in`'s types both
mention `D-prefix e` — so they are still defined through a single bundled recursion to
keep the combinatorics synchronized for Agda, with the public helpers as projections.

```agda
record EntryData {Γ : Ctx} (D : DTy Γ) (e : Entry D) : Set₁ where
  constructor mkEntryData
  field
    -- The prefix diagram at entry `e`
    prefix : DTy Γ
    -- The type at entry `e`
    entry-ty : Ty (Γ ▸▸ prefix)
    -- Assigning entries of the prefix to entries of `D`
    embed-entry : Entry prefix → Entry D

entry-data : {Γ : Ctx} → {D : DTy Γ} → (e : Entry D) → EntryData D e
-- For a diagram extension `D' ▸ᵈ A`, the prefix at the last entry is `D'`,
-- the type is `A`, and the assignment sends `e'` to `there e'`.
entry-data {Γ} {D = D' ▸ᵈ A} here =
  mkEntryData D' A there
-- If the entry is not the last one, we recurse.
entry-data {D = D' ▸ᵈ A} (there e) =
  let
    ed = entry-data {D = D'} e
  in
  mkEntryData
    (EntryData.prefix ed)
    (EntryData.entry-ty ed)
    (λ e' → there (EntryData.embed-entry ed e'))

-- Public helpers by projection from the bundled recursion.
D-prefix : {Γ : Ctx} {D : DTy Γ} → Entry D → DTy Γ
D-prefix {D = D} e = EntryData.prefix (entry-data {D = D} e)

A-ty : {Γ : Ctx} {D : DTy Γ} → (e : Entry D) → Ty (Γ ▸▸ (D-prefix {D = D} e))
A-ty {D = D} e = EntryData.entry-ty (entry-data {D = D} e)

prefix-in : {Γ : Ctx} {D : DTy Γ} → (e : Entry D) → Entry (D-prefix {D = D} e) → Entry D
prefix-in {D = D} e = EntryData.embed-entry (entry-data {D = D} e)
```
