# 4-Diagrams: Entry Point for the Diagram Layer

This is the current entry point for the `4-Diagrams` branch.

Right now the only implemented part is the telescope syntax for diagram types
and diagram terms, in `4a-Diagrams`. The later hom-type, morphism, variance,
and universality files are still expected to sit on top of naturality once that
branch is ready.

Mathematical reference:

- `MATH_REFERENCE.md`, Section 4
- `../Thoughts series/Thoughts18.tex`, `sec:diagram-types`

```agda
module 4-Diagrams where

open import 4a-Diagrams public
```
