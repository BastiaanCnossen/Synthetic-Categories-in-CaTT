# 4a-Diagrams: Diagram Types as Typed Telescopes

This file starts the `4-Diagrams` branch at the part that does not yet depend
on naturality.

Mathematically, a diagram type over a context `Gamma` is just a finite telescope
of types over `Gamma`. Each new component may depend on the earlier components.
A diagram term is then a section of that telescope: for each stage we choose a
term of the next component after substituting in the previously chosen
components.

For the Agda formalization, the key bookkeeping objects are:

- `dty-ctx A`: the iterated context extension determined by a diagram type `A`
- `dty-proj A : Sub (dty-ctx A) Gamma`: the projection that forgets the diagram
  variables and returns to the ambient context
- `dtm-sub a : Sub Gamma (dty-ctx A)`: the substitution classified by a diagram
  term `a`

So a diagram term should be thought of as a section of the telescope projection.
This is the right shape for the later naturality construction: if `a b : DTm A`,
then the future hom-type `(a ->_A b)` should arise by applying naturality to
the context `dty-ctx A`, selecting exactly the variables contributed by the
diagram telescope, and then substituting the two sections `dtm-sub a` and
`dtm-sub b`.

The main thing we still need from the naturality branch is therefore very
concrete:

- naturality of an iterated context extension `dty-ctx A`
- a selector for the variables added by the diagram telescope
- substitution of the two endpoint sections into the resulting naturality data

The code below keeps only the telescope layer and makes those future inputs
explicit.

```agda
module 4a-Diagrams where

open import 2b-Wrappers

mutual
  -- A diagram type over Gamma is a telescope of dependent types.
  data DTy (Gamma : Ctx) : Set where
    -- The empty diagram contributes no extra variables.
    dnil : DTy Gamma
    -- Extending a diagram type adds one more type over the context built so far.
    dsnoc : (A : DTy Gamma) -> Ty (dty-ctx A) -> DTy Gamma

  -- The context classified by a diagram type is the ambient context extended by
  -- all of its components.
  dty-ctx : {Gamma : Ctx} -> DTy Gamma -> Ctx
  dty-ctx {Gamma} dnil = Gamma
  dty-ctx (dsnoc A B) = dty-ctx A , B

  -- Every diagram telescope comes with its projection back to the ambient
  -- context, forgetting the diagram variables.
  dty-proj : {Gamma : Ctx} -> (A : DTy Gamma) -> Sub (dty-ctx A) Gamma
  dty-proj {Gamma} dnil = idS Gamma
  dty-proj (dsnoc A B) = dty-proj A ∘ wk

  -- A diagram term is a section of the telescope projection.
  data DTm {Gamma : Ctx} : (A : DTy Gamma) -> Set where
    -- The empty diagram term is the unique section of the empty telescope.
    tnil : DTm dnil
    -- To extend a diagram term, first choose the earlier components,
    -- then choose a new term in Gamma,
    -- and finally prove that it has the substituted type determined by those
    -- earlier choices.
    tsnoc :
      {A : DTy Gamma}
      {B : Ty (dty-ctx A)}
      -> (a : DTm A)
      -> (b : Tm Gamma)
      -> TmTyEqSub b B (dtm-sub a)
      -> DTm (dsnoc A B)

  -- A diagram term determines the substitution that lists all of its chosen
  -- components into the telescope context.
  dtm-sub : {Gamma : Ctx} {A : DTy Gamma} -> (a : DTm A) -> Sub Gamma (dty-ctx A)
  dtm-sub {Gamma} tnil = idS Gamma
  dtm-sub (tsnoc a b pb) = ⟨ dtm-sub a , b ⟩∶[ pb ]

  -- Forgetting the chosen section gives back the underlying telescope
  -- projection.
  dtm-proj : {Gamma : Ctx} {A : DTy Gamma} -> (a : DTm A) -> Sub (dty-ctx A) Gamma
  dtm-proj {A = A} _ = dty-proj A
```

## What This Buys Us Later

Once naturality is available, the hom-type of two diagram terms should be built
from the naturality of the telescope context `dty-ctx A` along the variables
coming from the diagram part. The endpoint substitutions will be precisely
`dtm-sub a` and `dtm-sub b`.

So the next diagram file should not start by inventing new syntax. It should
start from this telescope interface and ask naturality to act on:

1. the context `dty-ctx A`
2. the diagram-variable selector inside that context
3. the two sections `dtm-sub a` and `dtm-sub b`

That is the exact interface pressure this file is meant to expose.
