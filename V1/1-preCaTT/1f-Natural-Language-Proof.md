# Natural-Language Proof

This note explains the proof formalized in
`1f-FunctorialityPasting.lagda.md` after the cutover to structured pasting
selectors.

## Statement

Fix a pasting context `Gamma` with proof `Gammaps : CtxPs Gamma`. Instead of a
raw selector `X : Var Gamma -> Bool`, we work with a structured selector
`s : PsSel Gammaps`.

From `s` we get an ordinary boolean selector

`eval-ps-sel s : Var Gamma -> Bool`

and the theorem proves simultaneously:

1. `func-pasting Gammaps s` is a pasting context on the functorial image
   `Gamma ↑ eval-ps-sel s`.
2. Every dangling variable `xps : VarPs Gamma Gammaps` has an induced dangling
   variable `func-dangling xps s` in that image.
3. Its type is exactly the old type transported along `in^-`.
4. Its variable is exactly the old variable transported along `in^-`.

So the main theorem is still the same mathematical statement as before, but it
is expressed using a constructor-headed selector object rather than a raw
predicate plus a separate local-maximality proof.

## Why `PsSel`

The key formal issue in the raw development was that the extension step had to
branch on whether the newest variable was selected, while the goal still
contained unsimplified terms such as:

- `((ext-ctx xps) ↑ X)`
- `in^- (ext-ctx xps) X`

Those terms compute by inspecting `X vz`. In raw form, Agda repeatedly got
stuck trying to perform that branch while preserving the dependent types
mentioning the unbranched `X`.

`PsSel` removes that mismatch. A selector for an extension is already one of two
constructors:

- `unsplitSel s0 lm0 notSel`
- `splitSel s0 lm0 notSel`

So the branch is no longer hidden inside a raw function. The theorem recurses on
that structured selector directly.

## Induction on Pasting Contexts

The proof is a mutual recursion on the pasting structure:

- `func-pasting`
- `func-dangling`
- `func-dangling-type`
- `func-dangling-var`

This strengthening is essential. In the extension step one must produce not only
the new pasting context, but also the specific dangling witnesses that generate
its extension structure, together with the type and variable equalities needed
to identify the new hom-type correctly.

## Base Case

For `ps-ob` there are two selectors:

- `pssel-ob-unsplit`
- `pssel-ob-split`

If the unique object variable is not selected, the image stays `ps-ob`. If it is
selected, functoriality produces the arrow context, which is again a valid
pasting context. The dangling witness is immediate in both cases.

## Extension Step

Now let the pasting context be `ps-ext xps`, so the ambient context is
`ext-ctx xps`.

The structured selector `s : PsSel (ps-ext xps)` already tells us whether we are
in the unsplit or split branch. Its base part `prev-pssel s` is the selector on
the old context `Gamma`, and by the recursive hypothesis we get the induced
dangling witness

`d = func-dangling xps (prev-pssel s)`.

This `d` is the recursive witness from which the next pasting extension is built.

### Unsplit Branch

In the unsplit case, the new edge `f` is not selected. The functorial image of
`ext-ctx xps` aligns with

`ext-ctx d`.

So the dangling variables in the image are exactly the standard ones:

- `varps-f d`
- `varps-y d`
- `varps-weak d (...)`

The only work is to prove the context alignment and then transport these
standard witnesses across it.

### Split Branch

In the split case, the new edge `f` is selected. Local maximality forces the new
target `y` not to be selected, so the functorial image is the split extension
determined by `d`. Concretely it aligns with

`ext-ctx (varps-f d)`.

Then the dangling variables are:

- the image of `f`, now represented by `varps-y (varps-f d)`
- the image of `y`, represented by a weakened witness over `varps-f d`
- the image of any older dangling variable, represented by a further weakened
  witness

Again, once the alignment is known, the witnesses are the standard pasting ones
transported across that equality.

## Why the Type and Variable Equalities Matter

The recursive witness `d` is not enough by itself. To identify the functorial
image with the canonical pasting extension built from `d`, we also need:

- `func-dangling-type`, saying that the type of `d` is the old type transported
  along `in^-`
- `func-dangling-var`, saying that the variable of `d` is the old variable
  transported along `in^-`

Those two equalities are exactly what lets the functorialized extension type be
recognized as the hom-type of the recursive witness.

## Proof Shape in One Line

For an extension:

1. recurse on the base selector `prev-pssel s`
2. obtain the recursive witness `d`
3. identify the new functorial context with the appropriate standard extension
   built from `d`
4. transport the standard dangling witnesses across that alignment
5. use the recursive type and variable equalities to prove the transported
   witnesses have the expected types and variables

That is the complete mathematical content of the Agda development. The crucial
formal point is that the theorem is stated directly for `PsSel`, so the split is
constructor-headed from the start rather than reconstructed from a raw selector.
