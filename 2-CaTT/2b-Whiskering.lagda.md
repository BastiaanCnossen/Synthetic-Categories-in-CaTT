# Typed whiskering interface

This file is a stub. The whiskering operations should be defined roughly 
following the file Agda formalization\I-CaTT\archive\I-CaTT-V10\2-CaTT\2b-Whiskering.lagda.md. *However*, the new file should satisfy the following strict design criteria:
- It should from the ground up be written at the typed level
- It should be written in a fully relational way, avoiding the previous compute-heavy
  computational approach.
This stub file records the six postulates that eventually need to be defined.

```agda
module 2b-Whiskering where

import 2a-CaTT as CaTT

open import Data.Nat using (ℕ; suc)

open CaTT public

data itgt {Γ : Ctx} : Ty Γ → Tm Γ → Set₁ where
  itgt-base :
    {A : Ty Γ} {x y : Tm Γ}
    → (px : HasTy x A)
    → (py : HasTy y A)
    → itgt (homTy A x y px py) y
  itgt-step :
    {A : Ty Γ} {x y z : Tm Γ}
    → (px : HasTy x A)
    → (py : HasTy y A)
    → itgt A z
    → itgt (homTy A x y px py) z

data isrc {Γ : Ctx} : Ty Γ → Tm Γ → Set₁ where
  isrc-base :
    {A : Ty Γ} {x y : Tm Γ}
    → (px : HasTy x A)
    → (py : HasTy y A)
    → isrc (homTy A x y px py) x
  isrc-step :
    {A : Ty Γ} {x y z : Tm Γ}
    → (px : HasTy x A)
    → (py : HasTy y A)
    → isrc A z
    → isrc (homTy A x y px py) z

postulate
  right-whisker-ty :
    {Γ : Ctx} {B A : Ty Γ} {y z : Tm Γ}
    → (py : HasTy y B)
    → (pz : HasTy z B)
    → (g : Tm Γ)
    → (pg : HasTy g (homTy B y z py pz))
    → itgt A y
    → Ty Γ

  right-whisker-tm :
    {Γ : Ctx} {B A : Ty Γ} {y z : Tm Γ}
    → (py : HasTy y B)
    → (pz : HasTy z B)
    → (g : Tm Γ)
    → (pg : HasTy g (homTy B y z py pz))
    → (q : itgt A y)
    → {a : Tm Γ}
    → HasTy a A
    → Tm Γ

  right-whisker-tm-typed :
    {Γ : Ctx} {B A : Ty Γ} {y z : Tm Γ}
    → (py : HasTy y B)
    → (pz : HasTy z B)
    → (g : Tm Γ)
    → (pg : HasTy g (homTy B y z py pz))
    → (q : itgt A y)
    → {a : Tm Γ}
    → (pa : HasTy a A)
    → HasTy (right-whisker-tm {Γ = Γ} {B = B} {A = A} {y = y} {z = z}
                              py pz g pg q {a = a} pa)
            (right-whisker-ty {Γ = Γ} {B = B} {A = A} {y = y} {z = z}
                              py pz g pg q)

  left-whisker-ty :
    {Γ : Ctx} {B A : Ty Γ} {x y : Tm Γ}
    → (px : HasTy x B)
    → (py : HasTy y B)
    → (f : Tm Γ)
    → (pf : HasTy f (homTy B x y px py))
    → isrc A y
    → Ty Γ

  left-whisker-tm :
    {Γ : Ctx} {B A : Ty Γ} {x y : Tm Γ}
    → (px : HasTy x B)
    → (py : HasTy y B)
    → (f : Tm Γ)
    → (pf : HasTy f (homTy B x y px py))
    → (q : isrc A y)
    → {a : Tm Γ}
    → HasTy a A
    → Tm Γ

  left-whisker-tm-typed :
    {Γ : Ctx} {B A : Ty Γ} {x y : Tm Γ}
    → (px : HasTy x B)
    → (py : HasTy y B)
    → (f : Tm Γ)
    → (pf : HasTy f (homTy B x y px py))
    → (q : isrc A y)
    → {a : Tm Γ}
    → (pa : HasTy a A)
    → HasTy (left-whisker-tm {Γ = Γ} {B = B} {A = A} {x = x} {y = y}
                             px py f pf q {a = a} pa)
            (left-whisker-ty {Γ = Γ} {B = B} {A = A} {x = x} {y = y}
                             px py f pf q)
```
