# 0a-Logic: Basic Boolean Lemmas

This module collects small propositional lemmas over booleans that are reused across the development.

**Belongs here:** Pure boolean combinators (`∧`, `∨`, `not`) with no CaTT-specific content.
**Does NOT belong here:** Anything mentioning `Var`, `Ty`, `Tm`, `Sub`, dependency, or pasting.

```agda
module 0a-Logic where

open import Agda.Builtin.Equality
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not)
```

```agda
∧-trueˡ : {b c : Bool} → b ∧ c ≡ true → b ≡ true
∧-trueˡ {true}  {c} p = refl
∧-trueˡ {false} {c} ()

∧-trueʳ : {b c : Bool} → b ∧ c ≡ true → c ≡ true
∧-trueʳ {true}  {c} p = p
∧-trueʳ {false} {c} ()

∧-true-intro : {b c : Bool} → b ≡ true → c ≡ true → b ∧ c ≡ true
∧-true-intro {true}  pb pc = pc
∧-true-intro {false} () pc

∨-falseˡ : {b c : Bool} → b ∨ c ≡ false → b ≡ false
∨-falseˡ {false} {c} p = refl
∨-falseˡ {true} {c} ()

∨-falseʳ : {b c : Bool} → b ∨ c ≡ false → c ≡ false
∨-falseʳ {false} {c} p = p
∨-falseʳ {true} {c} ()

-- Convenient projections from a nested `a ∨ (b ∨ c) ≡ false` proof.
∨3-falseˡ : {a b c : Bool} → a ∨ (b ∨ c) ≡ false → a ≡ false
∨3-falseˡ {a} {b} {c} p = ∨-falseˡ {b = a} {c = b ∨ c} p

∨3-falseᵐ : {a b c : Bool} → a ∨ (b ∨ c) ≡ false → b ≡ false
∨3-falseᵐ {a} {b} {c} p =
  ∨-falseˡ {b = b} {c = c} (∨-falseʳ {b = a} {c = b ∨ c} p)

∨3-falseʳ : {a b c : Bool} → a ∨ (b ∨ c) ≡ false → c ≡ false
∨3-falseʳ {a} {b} {c} p =
  ∨-falseʳ {b = b} {c = c} (∨-falseʳ {b = a} {c = b ∨ c} p)

not-true→false : {b : Bool} → not b ≡ true → b ≡ false
not-true→false {false} p = refl
not-true→false {true} ()

false→not-true : {b : Bool} → b ≡ false → not b ≡ true
false→not-true {false} p = refl
false→not-true {true} ()

true→not-false : {b : Bool} → b ≡ true → not b ≡ false
true→not-false {true} p = refl
true→not-false {false} ()

∨-trueʳ-from-falseˡ :
  {b c : Bool} → b ≡ false → b ∨ c ≡ true → c ≡ true
∨-trueʳ-from-falseˡ {false} {c} pb p = p
∨-trueʳ-from-falseˡ {true} {c} () p

∨-trueˡ-from-falseʳ :
  {b c : Bool} → c ≡ false → b ∨ c ≡ true → b ≡ true
∨-trueˡ-from-falseʳ {true}  {_}     cf bvc = refl
∨-trueˡ-from-falseʳ {false} {.false} refl ()

∨-true-introˡ : {b c : Bool} → b ≡ true → b ∨ c ≡ true
∨-true-introˡ {true} pb = refl
∨-true-introˡ {false} ()

∨-true-introʳ : {b c : Bool} → c ≡ true → b ∨ c ≡ true
∨-true-introʳ {false} pc = pc
∨-true-introʳ {true} pc = refl

∧-falseʳ-from-trueˡ :
  {b c : Bool} → b ≡ true → b ∧ c ≡ false → c ≡ false
∧-falseʳ-from-trueˡ {true} {c} pb p = p
∧-falseʳ-from-trueˡ {false} {c} () p

∧-falseˡ-from-trueʳ : {b c : Bool} → b ∧ c ≡ false → c ≡ true → b ≡ false
∧-falseˡ-from-trueʳ {false} p pc = refl
∧-falseˡ-from-trueʳ {true} {false} p ()
∧-falseˡ-from-trueʳ {true} {true} ()

∧-false-introʳ : {b c : Bool} → c ≡ false → b ∧ c ≡ false
∧-false-introʳ {false} pc = refl
∧-false-introʳ {true} pc = pc

true≠false : {α : Set} → true ≡ false → α
true≠false ()

-- Boolean biconditional.
_iff_ : Bool → Bool → Bool
true  iff true  = true
true  iff false = false
false iff true  = false
false iff false = true

iff-refl : {b : Bool} → (b iff b) ≡ true
iff-refl {true} = refl
iff-refl {false} = refl

iff-trueʳ→trueˡ : {a b : Bool} → (a iff b) ≡ true → b ≡ true → a ≡ true
iff-trueʳ→trueˡ {true}  {true}  _ _ = refl
iff-trueʳ→trueˡ {true}  {false} _ ()
iff-trueʳ→trueˡ {false} {true}  () _
iff-trueʳ→trueˡ {false} {false} _ ()
```
