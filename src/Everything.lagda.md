<!-- SPDX-License-Identifier: AGPL-3.0-only -->
# Everything

Imports every module in the library. This is the target the continuous-integration
type-checker builds, so that a green check certifies the *whole* development —
including the universe-polymorphic eliminators, which the public umbrella
`QIITOrd` does not re-export.

```agda
{-# OPTIONS --cubical --safe #-}

module Everything where

open import QIITOrd
import QIITOrd.Eliminator
import QIITOrd.Eliminator.NonDependent
import QIITOrd.Order.Code.Base
```
