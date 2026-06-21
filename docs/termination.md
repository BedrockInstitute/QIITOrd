<!-- SPDX-License-Identifier: AGPL-3.0-only -->
# Eliminating `{-# TERMINATING #-}` from the recursive order on ordinals

This note explains how `QIITOrd` defines the recursive, *computing* order on the
QIIT ordinal type `Ord` **without** `{-# TERMINATING #-}` — the construction the
reference development left as “work in progress.” It has three parts:

1. **The problem.**
2. **What the library does.**
3. **How it works.**

One-line summary: the order-code `_≤ᵖ_` is defined as a single application of an
*external* eliminator (recursion on the first ordinal, routed through a recursor
already proved terminating), which makes it non-recursive and so dissolves the
termination obstruction; transitivity `≤ᶜ-trans` is then one nested structural
recursion on the *middle* ordinal, and soundness `encode≤` one recursion on the
`_≤_` derivation.

---

## 1. The problem

### 1.1 The setting

[`QIITOrd.Base`](../src/QIITOrd/Base.lagda.md) defines ordinals as a **quotient
inductive–inductive type (QIIT)** `Ord`, mutually with an inductive order `_≤_`:

```agda
data Ord where
  zero     : Ord
  suc      : Ord → Ord
  lim      : MonoSeq → Ord                       -- limit of a strictly increasing sequence
  l≡l      : fst f ≈ fst g → lim f ≡ lim g       -- bisimilar sequences give equal limits (path constructor)
  isSetOrd : isSet Ord                           -- set-truncation constructor

data _≤_ where
  z≤      : zero ≤ α
  s≤s     : α ≤ β → suc α ≤ suc β
  ≤l      : α ≤ f [ n ] → α ≤ lim f
  l≤      : (∀ n → f [ n ] ≤ α) → lim f ≤ α
  ≤-trans : isTrans' _≤_
  isProp≤ : isProp (α ≤ β)
```

Here `MonoSeq = Σ[ f ∈ (ℕ → Ord) ] isMonoSeq f`, and `f ≈ g` is the
*bisimulation* `f ≼ g × g ≼ f` with `f ≼ g = ∀ n → ∃[ m ] f n ≤ g m` (the `∃` is
a **propositional truncation**).

### 1.2 The goal: a recursive, propositional characterisation of `≤`

The inductive `_≤_` is a proposition only by fiat (the `isProp≤` constructor) and
does not *compute*. We want an equivalent order that does:

```agda
_≤ᵖ_ : Ord → Ord → hProp ℓ-zero      -- by recursion on both ordinals
_≤ᶜ_ : Ord → Ord → Type
α ≤ᶜ β = typ (α ≤ᵖ β)                -- the "Code": carrier of the hProp
encode≤ : α ≤ β → α ≤ᶜ β             -- soundness
```

with defining clauses such as `zero ≤ᵖ β = Unit`, `suc α ≤ᵖ suc β = α ≤ᵖ β`,
`suc α ≤ᵖ lim f = ∃[ n ] suc α ≤ᶜ fst f n`, `lim f ≤ᵖ lim g = fst f ≼ᶜ fst g`.
This is the standard **encode–decode** method. Defining `_≤ᵖ_` on the *path*
constructors `l≡l`/`isSetOrd` forces a companion bundle (transitivity of `≤ᶜ`,
the cofinality helpers, …) to be defined *simultaneously*, so everything lands in
one large mutual block.

### 1.3 Why it does not pass the termination checker

There are **two distinct** reasons, which must not be conflated:

* **Source 1 — truncation-unpacking.** Recursive calls take a witness `(m , H)`
  *unpacked from a propositional truncation* (via `rec`, or by matching `∣ m , H ∣₁`).
  Agda never sees a value extracted from a truncation as structurally smaller.

* **Source 2 — `_≤ᵖ_`’s two-argument recursion with “cross” re-entries.** `_≤ᵖ_`
  recurses on *two* ordinals and, through `≤ᶜ = typ ∘ ≤ᵖ`, re-enters itself at
  positions where the first argument becomes a subterm of the *second*. A correct
  measure is “the sum of the sizes of **both** ordinals,” but Agda’s checker only
  does lexicographic structural descent **per argument position** — it cannot add
  two positions together.

### 1.4 A known-hard problem

This is a port of `BrouwerTree/Code.agda` from the Kraus–Nordvall Forsberg–Xu
development. That artifact **also** marks the construction `{-# TERMINATING #-}`,
noting that calling the encode function “with arguments unpacked by truncation
recursion … is not seen as structurally smaller by Agda,” and that implementing
the workaround to avoid the flag is **work in progress**.

---

## 2. What the library does

The whole order-code is split across two modules, and **neither uses any pragma,
postulate, or hole**:

| function | reference / upstream | QIITOrd |
| --- | --- | --- |
| `_≤ᵖ_` | `TERMINATING` | **structural** — one application of the external eliminator ([`Order.Code.Base`](../src/QIITOrd/Order/Code/Base.lagda.md)) |
| `≤ᶜ-trans` | `TERMINATING` in ref.; `postulate` in some variants | **structural** — nested `elimProp`, middle-first lexicographic `(β,α,γ)` |
| `encode≤` | `TERMINATING` | **structural** — `≤-elimProp` on the `_≤_` derivation |
| `≤ᶜ-refl`, `≤ᶜs`, `≤ᶜl`, the `≼ᶜ` helpers | `TERMINATING` | **structural** — `elimProp` / truncation `rec` |

So `QIITOrd` goes **beyond** the reference artifact (which marks the whole block)
and beyond intermediate variants that isolate the pragma on `_≤ᵖ_` or postulate
transitivity: here the order-code is `--safe` and pragma-free end to end.

---

## 3. How it works

### 3.0 The two work-horse recursors

[`QIITOrd.Base`](../src/QIITOrd/Base.lagda.md) exports:

* `elimProp` — structural recursion on `Ord` into a **proposition-valued** family.
  It discharges the `l≡l`/`isSetOrd` path cases automatically (`isProp→PathP` /
  `isProp→SquareP`), and in the `lim` case hands back the induction hypothesis
  **already unpacked** as `∀ n → P (f [ n ])`.
* `≤-elimProp` — structural recursion on the **`_≤_` derivation**, whose `l≤`
  method additionally supplies the sequence’s *monotonicity* hypotheses.

The central idea: **routing a function through an external recursor makes it
non-recursive, so it escapes the failing strongly-connected component.**

### 3.1 `_≤ᵖ_` via an external eliminator — removing the pragma

The obstruction in §1.3 is *Source 2*, which lives entirely in `_≤ᵖ_`. We remove
it by defining `_≤ᵖ_` as an application of the eliminator of
[`QIITOrd.Eliminator.NonDependent`](../src/QIITOrd/Eliminator/NonDependent.lagda.md),
recursing on the **first** ordinal:

```agda
_≤ᵖ_ : Ord → Ord → hProp ;  α ≤ᵖ β = fst (elim α) β
```

Since `elim` is checked once, parametrically, inside the eliminator module, the
definition `_≤ᵖ_ = fst ∘ elim` is **non-recursive** in *this* module, and the
`_≤ᵖ_ ↔ ≤ᶜ-trans` cycle is dissolved.

**Carrier.** The second-argument `l≡l` coherence needs the predicate functions to
be *monotone*, which a bare `Ord → hProp` does not carry. So the eliminator’s
carrier **bundles each predicate with its monotonicity**, with `≦` being up-set
inclusion:

```agda
A     = Σ[ P ∈ (Ord → hProp) ] (∀ {x y} → x ≤ y → typ (P x) → typ (P y))
P ≦ Q = ∀ γ → typ (Q γ) → typ (P γ)
```

The `succ` method (defining `suc α ≤ᵖ_`) reproduces the problem one level down
and is handled by an **inner** eliminator on the second ordinal, whose own
`≤-elim` *delivers the monotonicity* the bundle needs. The `sup` method (defining
`lim α' ≤ᵖ_`) obtains its monotonicity **without circular transitivity**, using
the sequence’s *strict* monotonicity to bump a limit element into the existential
form and then stripping the successor back off. Full details are in the literate
source.

### 3.2 `≤ᶜ-trans` via nested `elimProp` — the key technique

Transitivity is the hardest piece. It is a **single** application of `elimProp`,
nested three deep — on the **middle** ordinal `β`, then the first `α`, then the
third `γ`:

```agda
≤ᶜ-trans {α} {β} {γ} H₁ H₂ = elimProp {P = P} … β α H₁ γ H₂  where
  P β = (α : Ord) → α ≤ᶜ β → (γ : Ord) → β ≤ᶜ γ → α ≤ᶜ γ
```

Two facts make it work:

* **It is not recursive.** The body is one application of the already-terminating
  `elimProp`; the induction hypotheses arrive pre-unpacked, so the truncation
  `rec` inside is used only to *select an existing hypothesis index*, never to
  make a fresh recursive call. This is exactly the “equivalent induction principle
  with arguments already unpacked” the reference describes.
* **The measure is correct.** Every clause of the original recursive `≤ᶜ-trans`
  strictly decreases the **middle-first** lexicographic order `(β, α, γ)` under
  the immediate-subterm relation, and none increases:

  | clause `(α,β,γ)` → recursive call | β | α | γ |
  | --- | --- | --- | --- |
  | `suc/suc/suc → α/β/γ`       | ↓ |   |   |
  | `lim/suc/suc → f n/suc/suc` | = | ↓ |   |
  | `suc/suc/lim → suc/suc/f n` | = | = | ↓ |
  | `suc/lim/suc → suc/f n/suc` | ↓ |   |   |
  | `lim/lim/suc → f n/g m/suc` | ↓ |   |   |
  | `lim/suc/lim → f n/suc/g m` | = | ↓ |   |
  | `suc/lim/lim → suc/f n/g m` | ↓ |   |   |
  | `lim/lim/lim → f n/g m/h k` | ↓ |   |   |

  (A *first-argument-first* order fails; **middle-first** is the right one,
  matching the reference’s remark that `Code-trans` is “triple-induction on
  ordinals.”)

The `l≡l`/`isSetOrd` cases of all three ordinals are discharged automatically by
the nested `elimProp`s — the explicit coherence boilerplate of the original
disappears.

### 3.3 `encode≤` via `≤-elimProp`

`encode≤ : α ≤ β → α ≤ᶜ β` is recursion on the `_≤_` *derivation*, hence one
application of `≤-elimProp`. Its hard `l≤` method needs `lim f ≤ᶜ α`, for which it
uses `≤-elimProp`’s second hypothesis — the sequence’s monotonicity
`∀ n → suc (f n) ≤ᶜ f (suc n)` — together with an inner `elimProp` on `α`. The
`l≡l`/`isSetOrd`/`isProp≤` cases are again automatic.

### 3.4 Avoiding a circularity trap

A *well-founded* implementation — `≤ᶜ-trans` by recursion on `Acc _<_ (β,α,γ)` —
is **circular** under `--safe`: proving `_<_` well-founded needs
`α < lim f → ∃ n. α < f n` (inversion of `≤l`), which itself needs the
encode–decode. The route above avoids this entirely: it realises the descent
**structurally** (through `elimProp`), never through `Acc _<_`.

### 3.5 Performance

Because `≤ᶜ = typ ∘ ≤ᵖ` reduces only by unfolding the *nested eliminators* of
[`Order.Code.Base`](../src/QIITOrd/Order/Code/Base.lagda.md), the terms Agda’s
metavariable solver sees are enormous, and the occurs-check over them dominates.
Two measures keep [`Order.Code`](../src/QIITOrd/Order/Code.lagda.md) fast
(≈1.5 s instead of tens of seconds):

1. `--lossy-unification`, and
2. ascribing every type explicitly at the few sites where an implicit argument of
   `≤ᶜ-trans` / `≤ᶜs` / `rec` would otherwise be *inferred* by unifying against a
   giant unfolded `≤ᶜ` term (see `encode≤`’s `l≤-case`).

`≤ᶜ` is not constructor-headed, so such implicits are not invertible; pinning them
by hand keeps the occurs-check cheap.

---

## References

* N. Kraus, F. Nordvall Forsberg, C. Xu.
  [*Type-Theoretic Approaches to Ordinals*](https://arxiv.org/abs/2208.03844).
* The artifact
  [`constructive-ordinals-in-hott`](https://bitbucket.org/nicolaikraus/constructive-ordinals-in-hott/src/master/),
  whose `BrouwerTree/Code.agda` is the structurally-identical `{-# TERMINATING #-}`
  construction this library refactors.
