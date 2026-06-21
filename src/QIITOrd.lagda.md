<!-- SPDX-License-Identifier: AGPL-3.0-only -->
# QIITOrd

The public entry point of the library. Importing `QIITOrd` re-exports, in one go,
the ordinal type and its order, the elementary constructor analysis and strict
order, and the termination-free recursive order-code:

* [`QIITOrd.Base`](QIITOrd/Base.lagda.md) — the QIIT `Ord`, the order `_≤_`, the
  eliminators `elimProp` / `≤-elimProp`, and basic order lemmas;
* [`QIITOrd.Properties`](QIITOrd/Properties.lagda.md) — distinguishing/inverting
  constructors, the strict order `_<_`, and limit lemmas;
* [`QIITOrd.Order.Code`](QIITOrd/Order/Code.lagda.md) — the computing order-code
  `_≤ᶜ_` with `≤ᶜ-refl`/`≤ᶜ-trans` and the soundness map `encode≤`.

The eliminator machinery (`QIITOrd.Eliminator`,
`QIITOrd.Eliminator.NonDependent`) is universe-polymorphic and so is imported
directly, with level arguments, where needed.

```agda
{-# OPTIONS --cubical --safe #-}

module QIITOrd where

open import QIITOrd.Base public
open import QIITOrd.Properties public
open import QIITOrd.Order.Code public
```
