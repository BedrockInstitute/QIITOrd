<!-- SPDX-License-Identifier: AGPL-3.0-only -->
# QIITOrd

[![Typecheck](https://github.com/choukh/QIITOrd/actions/workflows/typecheck.yml/badge.svg)](https://github.com/choukh/QIITOrd/actions/workflows/typecheck.yml)
[![Agda](https://img.shields.io/badge/Agda-2.8.0-blue)](https://github.com/agda/agda)
[![cubical](https://img.shields.io/badge/cubical-0.9-blue)](https://github.com/agda/cubical)
[![License: AGPL-3.0-only](https://img.shields.io/badge/license-AGPL--3.0--only-blue.svg)](https://www.gnu.org/licenses/agpl-3.0.html)

**Brouwer-tree ordinals as a quotient inductive-inductive type (QIIT) in Cubical
Agda — with a recursive, computing order relation defined *without*
`{-# TERMINATING #-}`.**

The whole development is written in literate Agda (`.lagda.md`): every code block
is explained in prose, so the source files double as a readable account of the
construction. Start from [`src/QIITOrd.lagda.md`](src/QIITOrd.lagda.md).

## Background

This library is a **refactoring** of the Brouwer-tree ordinal development in
Kraus, Nordvall Forsberg and Xu's
[`constructive-ordinals-in-hott`](https://bitbucket.org/nicolaikraus/constructive-ordinals-in-hott/src/master/)
(the `BrouwerTree/*` modules accompanying the paper
[*Type-Theoretic Approaches to Ordinals*](https://arxiv.org/abs/2208.03844)),
extracted into a standalone, dependency-light library and **resolving its
termination problem**.

In the original development, the recursive characterisation of the order — the
`Code` family, here `_≤ᶜ_` — is accepted only under `{-# TERMINATING #-}`, and the
paper explicitly leaves the structural justification as *“work in progress.”* The
difficulty is genuine: the order-code recurses on two ordinals with “cross”
re-entries that no per-argument structural measure can see decrease, compounded by
recursive calls through propositional truncations.

**QIITOrd carries that work out.** The order-code is defined as an application of
an *external* eliminator (recursion on the first ordinal, routed through a
recursor already proved terminating), which dissolves the recursion the checker
could not accept; transitivity is then a single nested structural recursion on the
*middle* ordinal. The result is a complete, `--safe`, **zero-pragma** account:

* no `{-# TERMINATING #-}`,
* no `postulate`,
* no holes,
* no axiom of choice — and `Ord` stays a genuine QIIT.

The method is documented in [`docs/termination.md`](docs/termination.md).

## What's inside

| Module | Contents |
| --- | --- |
| [`QIITOrd.Base`](src/QIITOrd/Base.lagda.md) | The QIIT `Ord` (`zero`/`suc`/`lim`/`l≡l`/`isSetOrd`) and its order `_≤_`, defined mutually; the prop-eliminators `elimProp` / `≤-elimProp`; basic order lemmas and `≤`-reasoning. |
| [`QIITOrd.Eliminator`](src/QIITOrd/Eliminator.lagda.md) | The general **dependent** eliminator (`elim` / `≤-elim`) with its path-coherence checklist. |
| [`QIITOrd.Eliminator.NonDependent`](src/QIITOrd/Eliminator/NonDependent.lagda.md) | The non-dependent specialisation used to build the order-code. |
| [`QIITOrd.Properties`](src/QIITOrd/Properties.lagda.md) | Distinguishing and inverting constructors (`isZero`, `isSuc`, `pred`, `suc-inj`, `s≤s-inv`, …); the strict order `_<_` and its theory; limit lemmas (`l≤l`, …). |
| [`QIITOrd.Order.Code.Base`](src/QIITOrd/Order/Code/Base.lagda.md) | The order-code `_≤ᵖ_ : Ord → Ord → hProp`, via the external eliminator — the step that removes `{-# TERMINATING #-}`. |
| [`QIITOrd.Order.Code`](src/QIITOrd/Order/Code.lagda.md) | `_≤ᶜ_ = typ ∘ _≤ᵖ_`; `≤ᶜ-refl` / `≤ᶜs` / `≤ᶜl`; **`≤ᶜ-trans`** (nested structural recursion); **`encode≤ : α ≤ β → α ≤ᶜ β`** (soundness). |
| [`QIITOrd`](src/QIITOrd.lagda.md) | Umbrella re-export of the public API. |

## Dependencies

| | Version |
| --- | --- |
| [Agda](https://github.com/agda/agda) | 2.8.0 |
| [cubical](https://github.com/agda/cubical) | 0.9 |

The library depends on **`cubical` only** — no Agda standard library. The few
binary-relation combinators it needs are taken from `Cubical.Relation.Binary`.
`--guardedness` is enabled library-wide because `cubical` 0.9 is built with it.

## Building

With Agda 2.8.0 and `cubical` 0.9 installed and registered in
`~/.agda/libraries`, register this library and type-check everything:

```sh
echo "$(pwd)/QIITOrd.agda-lib" >> ~/.agda/libraries
agda src/Everything.lagda.md
```

To use it from another project, add `QIITOrd` to your `.agda-lib`'s `depend`
field and `open import QIITOrd`.

## References

* N. Kraus, F. Nordvall Forsberg, C. Xu.
  [*Type-Theoretic Approaches to Ordinals*](https://arxiv.org/abs/2208.03844).
* N. Kraus, F. Nordvall Forsberg, C. Xu. *Connecting Constructive Notions of
  Ordinals in Homotopy Type Theory* (MFCS 2021) — the artifact
  [`constructive-ordinals-in-hott`](https://bitbucket.org/nicolaikraus/constructive-ordinals-in-hott/src/master/),
  whose `BrouwerTree/Code.agda` is the `{-# TERMINATING #-}` construction this
  library refactors.

## License

Licensed under the GNU Affero General Public License v3.0 only
([AGPL-3.0-only](LICENSE)).

This is a derivative of the Brouwer-tree development in
`constructive-ordinals-in-hott` by Nicolai Kraus, Fredrik Nordvall Forsberg and
Chuangjie Xu; all credit for the original mathematics is theirs.
