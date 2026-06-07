# 4b-DiagramHoms: diagram hom types

The basic object of this file is the **diagram hom over a source diagram**. Given
a source diagram `D` and a target diagram `E` (both over `Γ`), two sections

```text
d₁ d₂ : DTmOverDTy D E
```

each present a copy of `E` living over the source diagram context `Γ ▸▸ D`. Their
diagram hom `DHomOver d₁ d₂ H` recognizes `H : DTy (Γ ▸▸ D)` as the diagram type
whose entries compare the corresponding entries of `d₁` and `d₂`, naturalized in
the direction of the source-diagram variables.

Ordinary diagram homs are then the special case `D = ◆ᵈ`: a plain diagram term
`DTm E` is a section over the empty source diagram, and `DHom` is the resulting
`DHomOver` over `◆ᵈ`. Because `Γ ▸▸ ◆ᵈ` reduces to `Γ`, the derived `DHom` has the
familiar shape with carrier `DTy Γ`, with no transport.

The relation in this file records exactly the structure of the hom telescope
without computing a chosen output. The companion `4b-DiagramHoms-Comp` constructs
the chosen carriers `dhom-over d₁ d₂` and `dhom d₁ d₂` and proves that they satisfy
`DHomOver` / `DHom`.

```agda
module 4b-DiagramHoms where

open import Data.Empty using (⊥; ⊥-elim)

import 1a-RawSyntax as Raw
import 1b-Dependency as Dep
open import 2a-CaTT
open import 3a-UpClosed
import 3b-Naturality as Nat
open import 4a-Diagrams
```

## Diagram selectors

The diagram hom construction needs the up-closed selector that marks **exactly the
diagram variables** of a total context `Γ ▸▸ D`: the ambient variables of `Γ` are
unset, every entry of `D` is set. This is the relational analogue of the old `sel-∅`
and `dty-sel`.

```agda
mutual
  -- The empty selector marks no variable of Γ.
  sel-∅ : (Γ : Ctx) → Up Γ
  sel-∅ Γ with ctx-view Γ
  ... | ◆-view = mk Dep.sel-base base
  ... | ▸-view {Γ = Γ'} A =
    let X' = sel-∅ Γ'
    in mk (Dep.sel-unset (Raw-Ty A) (Up.sel X'))
         (snoc-unset (Up.sel X') (Up.is-upcl X') (sel-∅-indep Γ' A))

  sel-∅-no-select :
    (Γ : Ctx) → (x : Var Γ) → Dep.selects (Up.sel (sel-∅ Γ)) x → ⊥
  sel-∅-no-select Γ x px with ctx-view Γ | x | px
  ... | ◆-view            | ()         | _
  ... | ▸-view {Γ = Γ'} A | Raw.zero   | ()
  ... | ▸-view {Γ = Γ'} A | Raw.succ y | Dep.there-unset py =
        sel-∅-no-select Γ' y py

  sel-∅-indep :
    (Γ : Ctx) → (A : Ty Γ) → Dep.SelTypeIndep (Up.sel (sel-∅ Γ)) (Raw-Ty A)
  sel-∅-indep Γ A {x} px _ = ⊥-elim (sel-∅-no-select Γ x px)

-- The selector attached to a diagram telescope: every snoc-step sets the newest
-- (diagram) variable, ambient variables stay unset via sel-∅.
dty-sel : {Γ : Ctx} → (D : DTy Γ) → Up (Γ ▸▸ D)
dty-sel {Γ} ◆ᵈ = sel-∅ Γ
dty-sel (D ▸ᵈ A) =
  let X' = dty-sel D
  in mk (Dep.sel-set (Raw-Ty A) (Up.sel X')) (snoc-set (Up.sel X') (Up.is-upcl X'))
```

## The overal structure

Before defining the relation DHomOver, we recall how the construction of the diagram
hom is supposed to behave. For simplicity, we will explain the situation for the plain
diagram terms `e1` and  `e2` of a given a target diagram type `E`. (The general
framework requires us to work with diagram terms over a source diagram type `D`.) Then
there should be a new diagram type `dhom E e1 e2`, which comes equipped with a 
substitution ` dhom-sub E e1 e2 ` from `Γ ▸▸ (dhom E e1 e2)` to `↑ctx (Γ ▸▸ E)`,  which
sends each `e⁻` to `e1` and each `e⁺` to `e2`.

The diagram type `dhom E e1 e2` is defined by structural recursion on `E`:
- For `◆ᵈ`, both terms are `◆ᵗ`, and the diagram hom is simply `◆ᵈ`
- For `E ▸ᵈ A`, the terms are of the form `e1 ▸ᵗ a1` and `e2 ▸ᵗ a2`. 
  The diagram hom is then an extension of `dhom E d1 d2` by a type constructed as follows:
  (a) Perform the naturality of `A` w.r.t. `dty-sel`, giving a type in `↑ctx-ext (Γ ▸▸ E)`
  (b) Substitute this type along the substitution `dhom-sub E e1 e2`

We also define `dhom-sub E e1 e2` by structural recursion on `E`:
- For `◆ᵈ`, we use an explicitly defined substitution `dhom-base-sub`.
- For `E ▸ᵈ A`, we build the substitution in three steps from `dhom-sub E e1 e2`:
  (a) We first extend by the term `t⁻ = a1 [ proj ]t`
  (b) Then further by `t⁺ = a2 [ proj ]t`
  (c) And then finally by the last variable in `Γ ▸▸ (dhom E ▸ᵈ A)`

## The diagram-hom step relation

We should now turn this idea into a relation `DHomOver`. We will still recurse over
the target diagram `E`, building one new hom component per entry of `E`. We will now
spell out what data is needed to perform the inductive step for an extended diagram.

For an entry `A : Ty (Γ ▸▸ E)` of the target and the two endpoint terms 
`a₁ , a₂ : Tm (Γ ▸▸ D)` taken from the heads of the two sections, the new hom
component is built as

```text
A↑  :=  ↑ty (dty-sel E) A                        -- naturality type of A over (Γ ▸▸ E)↑
B   :=  A↑ [ comparison substitution ]T          -- reindexed into (Γ ▸▸ D) ▸▸ H
```

i.e. (1) take the naturality type `A↑` of the entry `A` with respect to the
**target** diagram selector `dty-sel E`, and (2) substitute it down into
`(Γ ▸▸ D) ▸▸ H` along the **comparison substitution** determined by the prefix hom and
the two endpoint terms, sending the suspended block via the prefix comparison and
the endpoint variables `x⁻ , x⁺` to `a₁ , a₂` weakened along the prefix hom. This is
the source-relativized analogue of the absolute construction over `Γ`: the base
context `Γ` is replaced by the source diagram context `Γ ▸▸ D` throughout.

Both steps are expressed through the abstract naturality interface:

- Step (1): `A↑` is recognized by `Nat.NatTy`.
- Step (2a): the comparison substitution from `(Γ ▸▸ D) ▸▸ H` into the *extended*
  naturality context is stored directly as the `ext` field of the step record below —
  an ordinary `Sub ((Γ ▸▸ D) ▸▸ H) Γ↑A`. The relational core only records *that* such a
  comparison substitution exists; the companion `4b-DiagramHoms-Comp` constructs the
  canonical one (`dhom-over-sub` / `dhom-over-sub-ext`) by recursion on the prefix hom.
- Step (2b): the endpoint terms `a₁ , a₂ : Tm (Γ ▸▸ D)` are seen as terms
  `a₁ᴴ , a₂ᴴ` of `(Γ ▸▸ D) ▸▸ H` via the relational weakening `DWkTm H`.
- Step (2c): acting on `A↑` along the stored extended comparison substitution is
  recorded directly by `Raw.SubstTy`.

Because `DHomStepTyOver` mentions `DHomOver` (through the prefix-hom evidence `h`), and
`DHomOver`'s snoc constructor mentions `DHomStepTyOver`, the two are arranged by
forward-declaring `DHomOver`'s signature first.

```agda
-- Forward signature for DHomOver (constructors are given further below).
data DHomOver {Γ : Ctx} {D : DTy Γ} :
    {E : DTy Γ} → DTmOverDTy D E → DTmOverDTy D E → DTy (Γ ▸▸ D) → Set₁
```

The step record consumes the prefix-hom evidence `h` and builds `B` as the action of
the extended comparison substitution on `A↑`:

```agda
record DHomStepTyOver
  {Γ : Ctx} {D E : DTy Γ} {H : DTy (Γ ▸▸ D)}
  {d₁ d₂ : DTmOverDTy D E}
  (h : DHomOver d₁ d₂ H)      -- proof that H is the hom of the prefix target E
  (A : Ty (Γ ▸▸ E))          -- the target entry type being naturalized
  (a₁ a₂ : Tm (Γ ▸▸ D))      -- the two new endpoint terms, over the source context
  (B : Ty ((Γ ▸▸ D) ▸▸ H))   -- candidate new hom component
  : Set₁ where
  field
    {Γ↑ Γ↑A} : Ctx
    -- (1) recognize the naturality type A↑ of A w.r.t. the target diagram selector
    nctx : Nat.NatCtx (Γ ▸▸ E) (dty-sel E) Γ↑
    next : Nat.NatCtxExt (dty-sel E) nctx A Γ↑A
    {A↑} : Ty Γ↑A
    nty  : Nat.NatTy (dty-sel E) nctx A next A↑
    -- (2b) endpoint terms weakened from Γ ▸▸ D into (Γ ▸▸ D) ▸▸ H
    {a₁ᴴ a₂ᴴ} : Tm ((Γ ▸▸ D) ▸▸ H)
    wk₁ : DWkTm H a₁ a₁ᴴ
    wk₂ : DWkTm H a₂ a₂ᴴ
    -- (2c) extend the prefix comparison substitution across x⁻, x⁺ and act on A↑
    ext     : Sub ((Γ ▸▸ D) ▸▸ H) Γ↑A
    reindex : Raw.SubstTy (Raw-Ty A↑) (Raw-Sub ext) (Raw-Ty B)

open DHomStepTyOver public
```

## The diagram-hom-over relation

`DHomOver d₁ d₂ H` says `H : DTy (Γ ▸▸ D)` is the diagram hom, over the source
diagram context `Γ ▸▸ D`, between the sections `d₁ d₂ : DTmOverDTy D E`. The source
diagram `D` is a parameter; the target diagram `E` is an index (it grows in the snoc
clause), and the two sections and the resulting hom are the explicit arguments. The
snoc constructor passes the prefix-hom proof `h` to `DHomStepTyOver`.

The empty-target case relates the two empty sections `◆ᴰ` to the empty diagram `◆ᵈ`
over `Γ ▸▸ D`. The snoc case takes the two endpoints from the heads of the two
`DTmOverDTy D (E ▸ᵈ A)` sections.

```agda
data DHomOver {Γ} {D} where
  dhomover-◆ :
    DHomOver ◆ᴰ ◆ᴰ ◆ᵈ

  dhomover-▸ :
    {E : DTy Γ} {A : Ty (Γ ▸▸ E)}
    {A′₁ A′₂ : Ty (Γ ▸▸ D)}
    {d₁ d₂ : DTmOverDTy D E} {a₁ a₂ : Tm (Γ ▸▸ D)}
    {p₁ : DSubstTyOver d₁ A A′₁} {q₁ : HasTy a₁ A′₁}
    {p₂ : DSubstTyOver d₂ A A′₂} {q₂ : HasTy a₂ A′₂}
    {H : DTy (Γ ▸▸ D)} {B : Ty ((Γ ▸▸ D) ▸▸ H)} →
    (h : DHomOver d₁ d₂ H) →
    DHomStepTyOver h A a₁ a₂ B →
    DHomOver (d₁ ▸ᴰ a₁ [ p₁ ][ q₁ ]) (d₂ ▸ᴰ a₂ [ p₂ ][ q₂ ]) (H ▸ᵈ B)
```

## Ordinary diagram homs as the empty-source special case

A plain diagram term `DTm E` is exactly a section over the empty source diagram. To
read it as one, `toOver` rebuilds a `DTm E` as a `DTmOverDTy ◆ᵈ E`, converting the
type-evaluation evidence along the way. Because `Γ ▸▸ ◆ᵈ` reduces to `Γ`, the
evaluated types and the entry terms keep their types definitionally; the variable
leaf's ambient case becomes the identity weakening `DWkTm ◆ᵈ` (i.e. `dwkTm-◆`),
matching the remark in `4a-Diagrams` that `SubstTyAtDTm` is the `◆ᵈ` case of
`DSubstTyOver`.

```agda
mutual
  toOver : {Γ : Ctx} {E : DTy Γ} → DTm E → DTmOverDTy ◆ᵈ E
  toOver ◆ᵗ = ◆ᴰ
  toOver (d ▸ᵗ a [ p ][ q ]) = toOver d ▸ᴰ a [ toOverTy p ][ q ]

  toOverTy :
    {Γ : Ctx} {D : DTy Γ} {d : DTm D} {A : Ty (Γ ▸▸ D)} {A′ : Ty Γ} →
    SubstTyAtDTm d A A′ → DSubstTyOver (toOver d) A A′
  toOverTy sty-⋆ = dsty-⋆
  toOverTy (sty-hom pA pt pu) =
    dsty-hom (toOverTy pA) (toOverTm pt) (toOverTm pu)

  toOverTm :
    {Γ : Ctx} {D : DTy Γ} {d : DTm D} {t : Tm (Γ ▸▸ D)} {t′ : Tm Γ} →
    SubstTmAtDTm d t t′ → DSubstTmOver (toOver d) t t′
  toOverTm (stm-var sv) = dstm-var (toOverVar sv)
  toOverTm (stm-coh ss) = dstm-coh (toOverSub ss)

  toOverSub :
    {Γ : Ctx} {D : DTy Γ} {d : DTm D} {Δ : Ctx}
    {σ : Sub (Γ ▸▸ D) Δ} {σ′ : Sub Γ Δ} →
    SubstSubAtDTm d σ σ′ → DSubstSubOver (toOver d) σ σ′
  toOverSub ssub-◆ = dssub-◆
  toOverSub (ssub-snoc ss st) = dssub-snoc (toOverSub ss) (toOverTm st)

  toOverVar :
    {Γ : Ctx} {D : DTy Γ} {d : DTm D} {x : Var (Γ ▸▸ D)} {t′ : Tm Γ} →
    SubstVarAtDTm d x t′ → DSubstVarOver (toOver d) x t′
  toOverVar sv-base       = dsv-base dwkTm-◆
  toOverVar sv-zero       = dsv-zero
  toOverVar (sv-succ sv)  = dsv-succ (toOverVar sv)
```

`DHom d₁ d₂ H` is then the empty-source hom of two diagram terms. Its carrier is
`DTy Γ` because `Γ ▸▸ ◆ᵈ` reduces to `Γ`, so no transport is needed.

```agda
DHom :
  {Γ : Ctx} {E : DTy Γ} →
  DTm E → DTm E → DTy Γ → Set₁
DHom d₁ d₂ H = DHomOver (toOver d₁) (toOver d₂) H
```

## Status and the naturality interface used

`DHomOver` is fully relational and recursive: the snoc constructor consumes a
`DHomOver` on the prefix plus a single `DHomStepTyOver` step. Ordinary `DHom` is
derived, not primitive. No chosen `dhom`, `↑`, `in⁻`, or `in⁺` appears here.

The naturality interface used is exactly the structured one from `3b-Naturality`:

- `Nat.NatTy` — recognizes the component naturality type `A↑`;
- `DWkTm H` — relational weakening of the two endpoint terms into `(Γ ▸▸ D) ▸▸ H`
  (real, from `4a-Diagrams`);
- direct `Sub` / `Raw.SubstTy` — the step record's `ext` field is an arbitrary extended
  comparison substitution `Sub ((Γ ▸▸ D) ▸▸ H) Γ↑A`, and `reindex` records its action on
  `A↑`. The core is purely a *specification*: it does not choose the comparison
  substitution.
