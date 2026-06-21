<!-- SPDX-License-Identifier: AGPL-3.0-only -->
# The antisymmetry-primitive variant, and why it cannot be `--safe`

This note records the outcome of an investigation into an **alternative presentation** of the
QIIT Brouwer ordinals, and explains why it is *not* included in the library: it cannot be made
fully `--safe` (zero `{-# TERMINATING #-}`), unlike the presentation we ship.

## The two presentations

QIITOrd ships the **transitivity-primitive** presentation (call it *ByTrans*):

```agda
data Ord where
  zero suc lim …
  l≡l      : fst f ≈ fst g → lim f ≡ lim g     -- bisimilar limits are equal (path constructor)
  isSetOrd : isSet Ord
data _≤_ where
  z≤ s≤s ≤l l≤
  ≤-trans : isTrans' _≤_                        -- transitivity is a constructor
  isProp≤ : isProp (α ≤ β)
```

Here antisymmetry `α ≤ β → β ≤ α → α ≡ β` is a (hard) *theorem*
([`QIITOrd.Order.Antisymmetry`](../src/QIITOrd/Order/Antisymmetry.lagda.md)).

The **antisymmetry-primitive** variant (*ByAntisym*) swaps which facts are primitive:

```agda
data Ord where
  zero suc lim …
  antisym  : α ≤ β → β ≤ α → α ≡ β              -- antisymmetry is the path constructor
  isSetOrd : isSet Ord
data _≤_ where
  z≤ s≤s ≤l l≤
  isProp≤                                        -- NO ≤-trans constructor
```

The two define the *same* ordered set (`antisym` collapses exactly the mutually-`≤` pairs, which
for limits is bisimilarity; `≤-trans` is admissible so dropping it as a constructor doesn't change
the relation). Antisymmetry is now free (`≤-antisym = antisym`), and `≤-trans` / `l≡l` would be
theorems.

## What was confirmed feasible (with one `{-# TERMINATING #-}`)

A scratch probe built ByAntisym with the order-code `_≤ᵖ_` defined by **direct** two-argument
recursion (the original style, needing `{-# TERMINATING #-}` for the cross-recursion), and it all
compiles: `≤ᶜ-trans`, `encode≤`, `decode≤`, and hence **`≤-trans`** (= `decode≤ ∘ ≤ᶜ-trans ∘
encode≤²`) and `l≡l`. In this `TERMINATING` setting the variant is in fact *simpler* than ByTrans:

- the `_≤ᵖ_` path-constructor faces collapse from ~10 `l≡l`/`isSetOrd` clauses (incl. a 4-face
  `l≡l × l≡l` square and an `isGroupoid` `l≡l × isSetOrd` corner) to **3 generic `antisym`
  clauses**, because the `antisym` face `(α ≤ᶜ γ) ≡ (β ≤ᶜ γ)` is *uniform in γ* — just
  left-composition `≤ᶜ-trans (encode p/q) _` — whereas the bisimulation face needs per-shape
  unpacking;
- the **four `≼`-cofinality helper lemmas vanish**;
- `≤-elimProp` and `encode≤` each lose their transitivity case;
- antisymmetry is free.

So as a *design*, the antisym presentation is attractive. The problem is making it **`--safe`**.

## Why fully `--safe` is blocked

The library's `--safe`, pragma-free order-code relies on the **external-eliminator** technique
([`QIITOrd.Order.Code.Base`](../src/QIITOrd/Order/Code/Base.lagda.md)): `_≤ᵖ_ = fst ∘ elim`, where
`elim` recurses on the first ordinal into the carrier `A` of *monotone* `hProp`-valued predicates.
Because `elim` is the already-terminating eliminator, `_≤ᵖ_` is non-recursive and needs no pragma.
Reproducing this for ByAntisym fails, for two reasons.

### Obstruction 1 — the `≤s` bootstrap (fixable)

The supremum method's monotonicity uses `≤s : α ≤ suc α`. In ByTrans `≤s` is free (its proof uses
the `≤-trans` *constructor*); in ByAntisym `≤s` provably needs general transitivity, which is only
available *after* the code — circular. This one is **fixable**: enrich the carrier with a
successor-monotonicity field `SucMono P = ∀ {x} → typ (P x) → typ (P (suc x))`, providable by
`zero`/`succ`/`sup` from the carried `SucMono` + `f≤l`-monotonicity, with no `≤s`.

### Obstruction 2 — the `antisym` face of the supremum predicate (fatal)

The carrier holds functions `P : Ord → hProp`. To **construct** the supremum element
`lim α' ≤ᵖ_ : Ord → hProp`, that function must be defined on *every* `Ord` constructor — including
**`antisym`**. The `antisym` case demands a path

```
(lim α' ≤ᶜ x) ≡ (lim α' ≤ᶜ y)      from   x ≤ y   and   y ≤ x
```

i.e. the predicate's *full monotonicity in both directions*. For this particular predicate, that
monotonicity **is the supremum property** of `lim α'` — which needs the predicate itself. The
resulting dependency is genuinely circular:

```
P_sup  (needs its antisym face)  →  mono_sup  →  the supremum bound  →  P_sup
```

and the only way to write it at all is a mutual block recursing across **both** `Ord` and `_≤_`
with cross-calls — exactly the pattern Agda's termination checker rejects (it is the original
`TERMINATING` problem, displaced one level). No carrier enrichment removes it: the obligation comes
from the `antisym` *constructor* being a path between **arbitrary** ordinals.

### The asymmetry with ByTrans

ByTrans escapes Obstruction 2 precisely because its path constructor **`l≡l` only quotients
limits**. So the predicate's coherence face is *concrete* — a path between two `∀ j ∃ m …`
limit-values — and is provable from element-monotonicity alone (`supPath`), never the full
supremum property. ByAntisym's `antisym` connects *arbitrary* ordinals, so the face is the full
monotonicity. The very `≤-trans` constructor that ByAntisym drops is what would have supplied this
monotonicity (as `≤s`) for free.

## Conclusion

The antisymmetry-primitive presentation is a real, equivalent, and in some respects simpler QIIT —
**but only with a `{-# TERMINATING #-}` on its order-code**. There is no fully `--safe`
construction of it by the external-eliminator method that makes ByTrans pragma-free, because the
`antisym` path constructor forces every `Ord → hProp` predicate (in particular the supremum) to
carry its full monotonicity at definition time, which for the order-code is circular.

Since a `--safe`, zero-pragma development is a defining property of this library, QIITOrd keeps the
**transitivity-primitive** presentation and does not ship the antisym variant. This document stands
as the record of why.
