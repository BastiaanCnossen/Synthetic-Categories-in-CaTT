```agda
module 2c-Examples where

open import Agda.Builtin.Equality
open import Data.Bool.Base using (true)
open import Data.Nat using (s≤s; z≤n)
open import Agda.Builtin.Sigma renaming (_,_ to _ʻ_)

open import 2a-CaTT using (⟨_,_⟩∶[_]; ⋆)
open import 2b-Wrappers hiding (TmTyEq; TmTyEqSub)
open import 1c-Pasting using
  ( ps-ob; ps-ext; varps-ob; varps-f; varps-y; varps-weak
  ; hom-type-ext-p-src; hom-type-ext-p-tgt )

-- Shorthand for the most recent variable term under a substitution into an extended context.
top : ∀ {Γ Δ} {A : Ty Γ} → Sub Δ (Γ , A) → Tm Δ
top {Γ} {A = A} σ = lookup (zero {Γ} {A}) σ

TmTyEq : ∀ {Γ} → Tm Γ → Ty Γ → Set
TmTyEq {Γ} t A = Raw-Ty (tyOf t) ≡ Raw-Ty A

TmTyEqSub : ∀ {Γ Δ} → Tm Γ → Ty Δ → Sub Γ Δ → Set
TmTyEqSub {Γ} {Δ} t A σ =
  Raw-Ty (tyOf t) ≡ Raw-Ty (A [ σ ]T)
```

```agda
Γ1 : Ctx
Γ1 = ∅ , ⋆

id1 : Sub Γ1 Γ1
id1 = idS Γ1

Γ-ob : Ctx
Γ-ob = Γ1

Γ-ob-ps : CtxPs Γ-ob
-- `(x : ⋆)` is the base pasting context.
Γ-ob-ps = ps-ob

x-ob : Tm Γ-ob
x-ob = top id1

-- Level 2: Add target object y
Γ2 : Ctx
-- Extend by a fresh object `y`.
Γ2 = Γ-ob , ⋆

wk2 : Sub Γ2 Γ-ob
wk2 = wk

id2 : Sub Γ2 Γ2
id2 = idS Γ2

-- Interlude: target object in Γ2
y-in-Γ2 : Tm Γ2
y-in-Γ2 = top id2

-- Level 3 type: f : x → y (using the exact V6 pasting helper)
ty-f : Ty Γ2
-- `x-ob [ wk2 ]t` transports `x` from Γ-ob into Γ2.
ty-f =
  [_]_⇒_:[_,_]
    { Γ2}
    ( ⋆)
    ( x-ob [ wk2 ]t)
    ( y-in-Γ2)
    ( refl)
    ( refl)

-- Level 3: Add morphism f
Γ3 : Ctx
Γ3 = Γ2 , ty-f

wk3 : Sub Γ3 Γ2
wk3 = wk

id3 : Sub Γ3 Γ3
id3 = idS Γ3

Γ-mor : Ctx
Γ-mor = Γ3

Γ-mor-ps : CtxPs Γ-mor
-- This is exactly the one-arrow pasting context.
Γ-mor-ps = ps-ext varps-ob

-- Generic variables
x-mor : Tm Γ-mor
x-mor = x-ob [ wk2 ]t [ wk3 ]t

y-mor : Tm Γ-mor
y-mor = top id2 [ wk3 ]t

f-mor : Tm Γ-mor
f-mor = top id3

-- Level 4: Add object z
Γ4 : Ctx
Γ4 = Γ-mor , ⋆

wk4 : Sub Γ4 Γ-mor
wk4 = wk

id4 : Sub Γ4 Γ4
id4 = idS Γ4

-- Interlude: object z in Γ4
z-in-Γ4 : Tm Γ4
z-in-Γ4 = top id4

-- Level 5 type: g : y → z
ty-g : Ty Γ4
-- Same pattern as `ty-f`, now with source `y` and target `z`.
ty-g = [ ⋆ ] ( y-mor [ wk4 ]t) ⇒ z-in-Γ4 :[ refl , refl ]

-- Level 5: Add morphism g
Γ5 : Ctx
Γ5 = Γ4 , ty-g

wk5 : Sub Γ5 Γ4
wk5 = wk

id5 : Sub Γ5 Γ5
id5 = idS Γ5

Γ-comp : Ctx
Γ-comp = Γ5

Γ-comp-ps : CtxPs Γ-comp
-- Choosing `varps-y varps-ob` yields the composable-arrows shape.
Γ-comp-ps = ps-ext (varps-y varps-ob)

-- Generic variables
x-comp : Tm Γ-comp
x-comp = x-mor [ wk4 ]t [ wk5 ]t

y-comp : Tm Γ-comp
y-comp = y-mor [ wk4 ]t [ wk5 ]t

z-comp : Tm Γ-comp
z-comp = (top id4) [ wk5 ]t

f-comp : Tm Γ-comp
f-comp = f-mor [ wk4 ]t [ wk5 ]t

g-comp : Tm Γ-comp
g-comp = top id5

-- Level 6: Add object w
Γ6 : Ctx
Γ6 = Γ-comp , ⋆

wk6 : Sub Γ6 Γ-comp
wk6 = wk

id6 : Sub Γ6 Γ6
id6 = idS Γ6

-- Interlude: object w in Γ6
w-in-Γ6 : Tm Γ6
w-in-Γ6 = top id6

-- Level 7 type: h : z → w
ty-h : Ty Γ6
ty-h = [ ⋆ ] (z-comp [ wk6 ]t) ⇒ w-in-Γ6 :[ refl , refl ]

-- Level 7: Add morphism h
Γ7 : Ctx
Γ7 = Γ6 , ty-h

wk7 : Sub Γ7 Γ6
wk7 = wk

id7 : Sub Γ7 Γ7
id7 = idS Γ7

Γ-assoc : Ctx
Γ-assoc = Γ7

Γ-assoc-ps : CtxPs Γ-assoc
-- Two successive `varps-y` choices encode a 3-arrow composable chain.
Γ-assoc-ps = ps-ext (varps-y (varps-y varps-ob))

-- Generic variables
x-assoc : Tm Γ-assoc
x-assoc = x-comp [ wk6 ]t [ wk7 ]t

y-assoc : Tm Γ-assoc
y-assoc = y-comp [ wk6 ]t [ wk7 ]t

z-assoc : Tm Γ-assoc
z-assoc = z-comp [ wk6 ]t [ wk7 ]t

w-assoc : Tm Γ-assoc
w-assoc = (top id6) [ wk7 ]t

f-assoc : Tm Γ-assoc
f-assoc = f-comp [ wk6 ]t [ wk7 ]t

g-assoc : Tm Γ-assoc
g-assoc = g-comp [ wk6 ]t [ wk7 ]t

h-assoc : Tm Γ-assoc
h-assoc = top id7

-- Level 8: Add the second 1-cell f'
mor-ty-mor : Ty Γ-mor
mor-ty-mor = wkTy ty-f

Γ8 : Ctx
Γ8 = Γ-mor , mor-ty-mor

wk8 : Sub Γ8 Γ-mor
wk8 = wk

id8 : Sub Γ8 Γ8
id8 = idS Γ8

-- Level 9 type: α : f ⇒ f'
f-in-Γ8 : Tm Γ8
f-in-Γ8 = _[_]t f-mor wk8

f'-in-Γ8 : Tm Γ8
f'-in-Γ8 = top id8

mor-ty-in-Γ8 : Ty Γ8
mor-ty-in-Γ8 = wkTy mor-ty-mor

ty-alpha : Ty Γ8
ty-alpha =
  [ mor-ty-in-Γ8 ] f-in-Γ8 ⇒ f'-in-Γ8 :[
    Ty-ext (hom-type-ext-p-src (varps-f varps-ob)) ,   
    Ty-ext (hom-type-ext-p-tgt (varps-f varps-ob)) ]

Γ9 : Ctx
Γ9 = Γ8 , ty-alpha

wk9 : Sub Γ9 Γ8
wk9 = wk

id9 : Sub Γ9 Γ9
id9 = idS Γ9

Γ-2cell : Ctx
Γ-2cell = Γ9

Γ-2cell-ps : CtxPs Γ-2cell
Γ-2cell-ps = ps-ext (varps-f varps-ob)

-- Generic variables
x-2cell : Tm Γ-2cell
x-2cell = x-mor [ wk8 ]t [ wk9 ]t

y-2cell : Tm Γ-2cell
y-2cell = y-mor [ wk8 ]t [ wk9 ]t

f-2cell : Tm Γ-2cell
f-2cell = f-mor [ wk8 ]t [ wk9 ]t

f'-2cell : Tm Γ-2cell
f'-2cell = (top id8)  [ wk9 ]t

α-2cell : Tm Γ-2cell
α-2cell = top id9

-- Level 10: Add object z (for whiskering)
rwhisk-xps : VarPs Γ-2cell Γ-2cell-ps
rwhisk-xps = varps-weak (varps-f varps-ob) (varps-y varps-ob) (s≤s z≤n)

ty-rwhisk-ob : Ty Γ-2cell
ty-rwhisk-ob = varps-to-type rwhisk-xps

Γ10 : Ctx
Γ10 = Γ-2cell , ty-rwhisk-ob

wk10 : Sub Γ10 Γ-2cell
wk10 = wk

id10 : Sub Γ10 Γ10
id10 = idS Γ10

-- Interlude: object z in Γ10
z-in-Γ10 : Tm Γ10
z-in-Γ10 = top id10

-- Level 11 type: g : y → z
ty-g-rwhisk : Ty Γ10
ty-g-rwhisk = [ ⋆ ] (y-2cell [ wk10 ]t)⇒ z-in-Γ10 :[ refl , refl ]

Γ11 : Ctx
Γ11 = Γ10 , ty-g-rwhisk

wk11 : Sub Γ11 Γ10
wk11 = wk

id11 : Sub Γ11 Γ11
id11 = idS Γ11

Γ-rwhisk : Ctx
Γ-rwhisk = Γ11

Γ-rwhisk-ps : CtxPs Γ-rwhisk
Γ-rwhisk-ps = ps-ext rwhisk-xps

-- Generic variables
x-rwhisk : Tm Γ-rwhisk
x-rwhisk = x-2cell [ wk10 ]t [ wk11 ]t

y-rwhisk : Tm Γ-rwhisk
y-rwhisk = y-2cell [ wk10 ]t [ wk11 ]t

z-rwhisk : Tm Γ-rwhisk
z-rwhisk = (top id10) [ wk11 ]t

f-rwhisk : Tm Γ-rwhisk
f-rwhisk = f-2cell [ wk10 ]t [ wk11 ]t

f'-rwhisk : Tm Γ-rwhisk
f'-rwhisk = f'-2cell [ wk10 ]t [ wk11 ]t

α-rwhisk : Tm Γ-rwhisk
α-rwhisk = α-2cell [ wk10 ]t [ wk11 ]t

g-rwhisk : Tm Γ-rwhisk
g-rwhisk = top id11

-- Part 2: Substitutions

sub-ob : {Γ : Ctx} → (x : Tm Γ) → (p : TmTyEqSub x ⋆ ∅S) → Sub Γ Γ-ob
sub-ob x p = ⟨ ∅S , x ⟩∶[ p ]


sub-ob2 : {Γ : Ctx}
        → (x y : Tm Γ)
        → (px : TmTyEqSub x ⋆ ∅S)
        → (py : TmTyEqSub   y ⋆ (sub-ob x px))
        → Sub Γ Γ2
sub-ob2 x y px py = ⟨ sub-ob x px , y ⟩∶[ py ]   

sub-mor : {Γ : Ctx}
        → (x y : Tm Γ)
        → (px : TmTyEqSub x ⋆ ∅S)
        → (py : TmTyEqSub y ⋆ (sub-ob x px))
        → (f : Tm Γ)
        → (pf : TmTyEqSub f ty-f (sub-ob2 x y px py))
        → Sub Γ Γ-mor
sub-mor x y px py f pf = ⟨ sub-ob2 x y px py , f ⟩∶[ pf ]   

sub-mor+ : {Γ : Ctx}
        → (x y z : Tm Γ)
         → (px : TmTyEqSub x ⋆ ∅S)
         → (py : TmTyEqSub   y ⋆ (sub-ob x px))
         → (f : Tm Γ)
         → (pf : TmTyEqSub   f ty-f (sub-ob2 x y px py))
         → (pz : TmTyEqSub   z ⋆ (sub-mor x y px py f pf))
         → Sub Γ Γ4
sub-mor+ x y z px py f pf pz = ⟨ sub-mor x y px py f pf , z ⟩∶[ pz ]

sub-comp : {Γ : Ctx}
         → (x y z : Tm Γ)
         → (px : TmTyEqSub x ⋆ ∅S)
         → (py : TmTyEqSub   y ⋆ (sub-ob x px))
         → (f : Tm Γ)
         → (pf : TmTyEqSub   f ty-f (sub-ob2 x y px py))
         → (pz : TmTyEqSub   z ⋆ (sub-mor x y px py f pf))
         → (g : Tm Γ)
         → (pg : TmTyEqSub   g ty-g
                              (sub-mor+ x y z px py f pf pz))
         → Sub Γ Γ-comp
sub-comp x y z px py f pf pz g pg = ⟨ sub-mor+ x y z px py f pf pz , g ⟩∶[ pg ]


sub-comp+ : {Γ : Ctx}
          → (x y z w : Tm Γ)
          → (px : TmTyEqSub x ⋆ ∅S)
          → (py : TmTyEqSub y ⋆ (sub-ob x px))
          → (f : Tm Γ)
          → (pf : TmTyEqSub f ty-f (sub-ob2 x y px py))
          → (pz : TmTyEqSub z ⋆ (sub-mor x y px py f pf))
          → (g : Tm Γ)
          → (pg : TmTyEqSub g ty-g
                               (sub-mor+ x y z px py f pf pz))
          → (pw : TmTyEqSub w ⋆ (sub-comp x y z px py f pf pz g pg))
          → Sub Γ Γ6
sub-comp+ x y z w px py f pf pz g pg pw = ⟨ sub-comp x y z px py f pf pz g pg , w ⟩∶[ pw ]   

sub-assoc : {Γ : Ctx}
          → (x y z w : Tm Γ)
          → (px : TmTyEqSub x ⋆ ∅S)
          → (py : TmTyEqSub y ⋆ (sub-ob x px))
          → (f : Tm Γ)
          → (pf : TmTyEqSub f ty-f (sub-ob2 x y px py))
          → (pz : TmTyEqSub z ⋆ (sub-mor x y px py f pf))
          → (g : Tm Γ)
          → (pg : TmTyEqSub g ty-g
                              (sub-mor+ x y z px py f pf pz))
          → (pw : TmTyEqSub w ⋆ (sub-comp x y z px py f pf pz g pg))
          → (h : Tm Γ)
          → (ph : TmTyEqSub h ty-h
                               (sub-comp+ x y z w px py f pf pz g pg pw))
          → Sub Γ Γ-assoc
sub-assoc x y z w px py f pf pz g pg pw h ph =
  ⟨ sub-comp+ x y z w px py f pf pz g pg pw , h ⟩∶[ ph ]   

sub-2cell : {Γ : Ctx}
          → (x y : Tm Γ)
          → (px : TmTyEqSub x ⋆ ∅S)
          → (py : TmTyEqSub y ⋆ (sub-ob x px))
          → (f : Tm Γ)
          → (pf : TmTyEqSub f ty-f (sub-ob2 x y px py))
          → (f' : Tm Γ)
          → (pf' : TmTyEqSub f' mor-ty-mor (sub-mor x y px py f pf))
          → (α : Tm Γ)
          → (pα : TmTyEqSub α ty-alpha
                               (⟨ sub-mor x y px py f pf , f' ⟩∶[ pf' ]))
          → Sub Γ Γ-2cell
sub-2cell x y px py f pf f' pf' α pα = ⟨ ⟨ sub-mor x y px py f pf , f' ⟩∶[ pf' ] , α ⟩∶[ pα ]   

sub-rwhisk : {Γ : Ctx}
           → (x y z : Tm Γ)
           → (px : TmTyEqSub x ⋆ ∅S)
           → (py : TmTyEqSub y ⋆ (sub-ob x px))
           → (f : Tm Γ)
           → (pf : TmTyEqSub f ty-f (sub-ob2 x y px py))
           → (f' : Tm Γ)
           → (pf' : TmTyEqSub f' mor-ty-mor (sub-mor x y px py f pf))
           → (α : Tm Γ)
           → (pα : TmTyEqSub α
                    ty-alpha
                    (⟨ sub-mor x y px py f pf , f' ⟩∶[ pf' ]))
           → (pz : TmTyEqSub z ty-rwhisk-ob
                                (sub-2cell x y px py f pf f' pf' α pα))
           → (g : Tm Γ)
           → (pg : TmTyEqSub g ty-g-rwhisk
                                (⟨ sub-2cell x y px py f pf f' pf' α pα , z ⟩∶[ pz ]))
           → Sub Γ Γ-rwhisk
sub-rwhisk x y z px py f0 pf0 f'0 pf'0 α pα pz g pg =
  ⟨ ⟨ sub-2cell x y px py f0 pf0 f'0 pf'0 α pα , z ⟩∶[ pz ] , g ⟩∶[ pg ]   


-- Part 3: Coherences

id-coh : {Γ : Ctx} → (x : Tm Γ) → (p : TmTyEqSub x ⋆ ∅S) → Tm Γ
id-coh x p =
  coh
    Γ-ob-ps
    ⋆
    x-ob
    x-ob
    refl
    refl
    refl
    (sub-ob x p)

comp-coh : {Γ : Ctx} {x y z : Tm Γ}
        → (px : TmTyEqSub x ⋆ ∅S)
        → (py : TmTyEqSub y ⋆ (sub-ob x px))
        → (f : Tm Γ)
        → (pf : TmTyEqSub f ty-f (sub-ob2 x y px py))
        → (pz : TmTyEqSub z ⋆ (sub-mor x y px py f pf))
        → (g : Tm Γ)
        → (pg : TmTyEqSub g ty-g (sub-mor+ x y z px py f pf pz))
        → Tm Γ
comp-coh {x = x} {y} {z} px py f pf pz g pg =
 coh
   Γ-comp-ps
   ⋆
   x-comp
   z-comp
   refl
   refl
   refl
   (sub-comp x y z px py f pf pz g pg)

lunit-coh : {Γ : Ctx} {x y : Tm Γ}
         → (px : TmTyEqSub x ⋆ ∅S)
         → (py : TmTyEqSub y ⋆ (sub-ob x px))
         → (f : Tm Γ)
         → (pf : TmTyEqSub f ty-f (sub-ob2 x y px py))
         → Tm Γ
lunit-coh {x = x} {y} px py f pf =
 coh
     Γ-mor-ps
     ([_]_⇒_:[_,_] ⋆ x-mor y-mor refl refl)
     (comp-coh {x = x-mor} {y-mor} {y-mor}
       refl
       refl
       f-mor
       refl
       refl
       (id-coh y-mor refl)
       refl)
     f-mor
     refl
     refl
     refl
     (sub-mor x y px py f pf)

runit-coh : {Γ : Ctx} {x y : Tm Γ}
         → (px : TmTyEqSub x ⋆ ∅S)
         → (py : TmTyEqSub y ⋆ (sub-ob x px))
         → (f : Tm Γ)
         → (pf : TmTyEqSub f ty-f (sub-ob2 x y px py))
         → Tm Γ
runit-coh {x = x} {y} px py f pf =
 coh
     Γ-mor-ps
     ([_]_⇒_:[_,_] {Γ-mor} ⋆ x-mor y-mor refl refl)
     (comp-coh {x = x-mor} {x-mor} {y-mor}
       refl
       refl
       (id-coh x-mor refl)
       refl
       refl
       f-mor
       refl)
     f-mor
     refl
     refl
     refl
     (sub-mor x y px py f pf)

assoc-coh : {Γ : Ctx} {x y z w : Tm Γ}
         → (px : TmTyEqSub x ⋆ ∅S)
         → (py : TmTyEqSub   y ⋆ (sub-ob x px))
         → (f : Tm Γ)
         → (pf : TmTyEqSub   f ty-f (sub-ob2 x y px py))
         → (pz : TmTyEqSub   z ⋆ (sub-mor x y px py f pf))
         → (g : Tm Γ)
         → (pg : TmTyEqSub   g ty-g (sub-mor+ x y z px py f pf pz))
         → (pw : TmTyEqSub   w ⋆ (sub-comp x y z px py f pf pz g pg))
         → (h : Tm Γ)
         → (ph : TmTyEqSub   h ty-h (sub-comp+ x y z w px py f pf pz g pg pw))
         → Tm Γ
assoc-coh {x = x} {y} {z} {w} px py f pf pz g pg pw h ph =
 coh
     Γ-assoc-ps
     ([_]_⇒_:[_,_] {Γ-assoc} (⋆) x-assoc w-assoc refl refl)
     (comp-coh {x = x-assoc} {y = y-assoc} {z = w-assoc}
       refl
       refl
       f-assoc
       refl
       refl
       (comp-coh {x = y-assoc} {y = z-assoc} {z = w-assoc}
         refl
         refl
         g-assoc
         refl
         refl
         h-assoc
         refl)
       refl)
     (comp-coh {x = x-assoc} {y = z-assoc} {z = w-assoc}
       refl
       refl
       (comp-coh {x = x-assoc} {y = y-assoc} {z = z-assoc}
         refl
         refl
         f-assoc
         refl
         refl
         g-assoc
         refl)
       refl
       refl
       h-assoc
       refl)
     refl
     refl
     refl
     (sub-assoc x y z w px py f pf pz g pg pw h ph)

rwhisk-coh : {Γ : Ctx} {x y z : Tm Γ}
          → (px : TmTyEqSub x ⋆ ∅S)
          → (py : TmTyEqSub   y ⋆ (sub-ob x px))
          → (f : Tm Γ)
          → (pf : TmTyEqSub   f ty-f (sub-ob2 x y px py))
          → (f' : Tm Γ)
          → (pf' : TmTyEqSub   f' mor-ty-mor (sub-mor x y px py f pf))
          → (α : Tm Γ)
          → (pα : TmTyEqSub   α ty-alpha
                               (⟨_,_⟩∶[_]   
                                 (sub-mor x y px py f pf)
                                 f'
                                 pf'))
          → (pz : TmTyEqSub   z ty-rwhisk-ob
                               (sub-2cell x y px py f pf f' pf' α pα))
          → (g : Tm Γ)
          → (pg : TmTyEqSub   g ty-g-rwhisk
                               (⟨_,_⟩∶[_]   
                                 (sub-2cell x y px py f pf f' pf' α pα)
                                 z
                                 pz))
          → Tm Γ
rwhisk-coh {x = x} {y} {z} px py f0 pf0 f' pf' α pα pz g pg =
 coh
     Γ-rwhisk-ps
     ([_]_⇒_:[_,_] (⋆) x-rwhisk z-rwhisk refl refl)
     (comp-coh {x = x-rwhisk} {y = y-rwhisk} {z = z-rwhisk}
       refl
       refl
       f-rwhisk
       refl
       refl
       g-rwhisk
       refl)
     (comp-coh {x = x-rwhisk} {y = y-rwhisk} {z = z-rwhisk}
       refl
       refl
       f'-rwhisk
       refl
       refl
       g-rwhisk
       refl)
     refl
     refl
     refl
     (sub-rwhisk x y z px py f0 pf0 f' pf' α pα pz g pg)
```
