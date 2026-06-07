# 1-preCaTT: PreCaTT Re-Export Module

This module is the entry point for the V7 `1-preCaTT` branch.

It re-exports the raw/pre-syntax computational layers used by the active CaTT
development:
- pre-syntax core (`1a-preCaTT`)
- dependency analysis (`1b-Dep`)
- pasting contexts (`1c-Pasting`)
- fullness conditions (`1d-Fullness`)

The later functoriality files `1e` and `1f` are intentionally kept out of this
small re-export surface: they are more specialized, heavier to type-check, and
are usually imported only by developments that explicitly need functoriality.

```agda
module 1-preCaTT where

import 1a-preCaTT as Pre public
import 1b-Dep as Dep public
import 1c-Pasting as Pasting public
import 1d-Fullness as Fullness public
```
