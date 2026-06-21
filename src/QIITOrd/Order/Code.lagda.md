<!-- SPDX-License-Identifier: AGPL-3.0-only -->
# The order-code: transitivity and soundness

This module completes the order-code. On top of the non-recursive
`_≤ᵖ_ : Ord → Ord → hProp` from `QIITOrd.Order.Code.Base`, it defines the
computing order `_≤ᶜ_ = typ ∘ _≤ᵖ_` and proves it is a reflexive, transitive
relation that `_≤_` *encodes into*:

* `≤ᶜ-refl`, `≤ᶜs`, `≤ᶜl` — the code analogues of `≤-refl`, `≤s`, `≤l`;
* `≤ᶜ-trans` — **transitivity**, the hardest piece, by nested structural
  recursion on the *middle* ordinal;
* `encode≤ : α ≤ β → α ≤ᶜ β` — soundness, by recursion on the `_≤_` derivation.

Together with `QIITOrd.Order.Code.Base`, this is a **complete, `--safe`,
`{-# TERMINATING #-}`-free** account of the recursive order — the construction the
[reference paper](https://arxiv.org/abs/2208.03844) left as "work in progress".
See [`docs/termination.md`](../../../docs/termination.md) for the full method.

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}
module QIITOrd.Order.Code where
open import QIITOrd.Base
open import QIITOrd.Properties
import QIITOrd.Order.Code.Base as V

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty using (⊥; isProp⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open BinaryRelation using (isRefl'; isTrans')
```

**Performance note.** Because `_≤ᶜ_ = typ ∘ _≤ᵖ_` now reduces only by unfolding
the *nested eliminators* of `QIITOrd.Order.Code.Base`, the terms Agda's
metavariable solver sees are enormous, and its occurs-check over them is the
dominant cost. Two measures keep this file fast (≈1.5 s from scratch instead of
tens of seconds): `--lossy-unification`, and ascribing every type explicitly at
the few sites where an implicit of `≤ᶜ-trans` / `≤ᶜs` / `rec` would otherwise be
*inferred* by unifying against one of those giant unfolded terms (see `encode≤`'s
`l≤-case`). `_≤ᶜ_` is not constructor-headed, so such implicits are not
invertible; pinned by hand, the occurs-check stays cheap.

## Signatures

We forward-declare `_≤ᵖ_` (defined below by delegation to `V`), then `_≤ᶜ_` and
the cofinality preorder `_≼ᶜ_` on sequences. The `_≼ᶜ_` is spelled out directly
(rather than via the generic `Bisimulation`) so the structural descent
`fst f n ≤ᶜ fst g m` stays visible. We then declare the five order facts that are
defined mutually further down.

```agda
_≤ᵖ_ : Ord → Ord → hProp ℓ-zero

_≤ᶜ_ : Ord → Ord → Type
α ≤ᶜ β = typ (α ≤ᵖ β)

_≼ᶜ⟨_⟩_ : (ℕ → Ord) → ℕ → (ℕ → Ord) → Type
f ≼ᶜ⟨ n ⟩ g = ∃[ m ∈ ℕ ] f n ≤ᶜ g m

_≼ᶜ_ : (ℕ → Ord) → (ℕ → Ord) → Type
f ≼ᶜ g = ∀ n → f ≼ᶜ⟨ n ⟩ g

≤ᶜ-refl  : isRefl' _≤ᶜ_
≤ᶜs      : α ≤ᶜ suc α
≤ᶜl      : α ≤ᶜ f [ n ] → α ≤ᶜ lim f
≤ᶜ-trans : isTrans' _≤ᶜ_
encode≤  : α ≤ β → α ≤ᶜ β

isProp≤ᶜ : isProp (α ≤ᶜ β)
isProp≤ᶜ {α} {β} = str (α ≤ᵖ β)

f≤ᶜl : f [ n ] ≤ᶜ lim f
f≤ᶜl = ≤ᶜl ≤ᶜ-refl
```

## Cofinality-transitivity helpers

Four small lemmas relate `_≼ᶜ_` (cofinality for the *code*) and `_≼_`
(cofinality for `_≤_`), each obtained by the propositional-truncation recursor
`rec` (so they are non-recursive pass-throughs). They round out the `_≼ᶜ_` API.

```agda
∃[n]≤ᶜ : (f g : MonoSeq) → fst f ≼ fst g → ∃[ n ∈ ℕ ] α ≤ᶜ fst f n → ∃[ n ∈ ℕ ] α ≤ᶜ fst g n
∃[n]≤ᶜ f g f≼g = rec squash₁ λ { (m , H₁) →
  rec squash₁ (λ { (k , H₂) → ∣ k , ≤ᶜ-trans H₁ (encode≤ H₂) ∣₁ }) (f≼g m) }

∀[n]≤ᶜ : (g f : MonoSeq) → fst g ≼ fst f → (∀ n → fst f n ≤ᶜ β) → (∀ n → fst g n ≤ᶜ β)
∀[n]≤ᶜ g f g≼f H₁ n = rec isProp≤ᶜ (λ { (m , H₂) → ≤ᶜ-trans (encode≤ H₂) (H₁ m) }) (g≼f n)

≼ᶜ-≼-trans : (g h f : MonoSeq) → fst g ≼ fst h → fst f ≼ᶜ fst g → fst f ≼ᶜ fst h
≼ᶜ-≼-trans g h f g≼h f≼ᶜg n = rec squash₁ (λ { (m , H₁) →
  rec squash₁ (λ { (k , H₂) → ∣ k , ≤ᶜ-trans H₁ (encode≤ H₂) ∣₁ }) (g≼h m) }) (f≼ᶜg n)

≼-≼ᶜ-trans : (g f h : MonoSeq) → fst g ≼ fst f → fst f ≼ᶜ fst h → fst g ≼ᶜ fst h
≼-≼ᶜ-trans g f h g≼f f≼ᶜh n = rec squash₁ (λ { (m , H₁) →
  rec squash₁ (λ { (k , H₂) → ∣ k , ≤ᶜ-trans (encode≤ H₁) H₂ ∣₁ }) (f≼ᶜh m) }) (g≼f n)
```

## The base cases of the code

`_≤ᵖ_` delegates to the eliminator-built definition (non-recursive). The three
base facts — reflexivity, `α ≤ᶜ suc α`, and the upper-bound `≤ᶜl` — are each one
`elimProp` on the first ordinal. The `≤ᶜl` limit case carefully uses the `elimProp`
hypothesis instead of `f≤ᶜl`, breaking what would otherwise be a `≤ᶜl ↔ f≤ᶜl`
cycle.

```agda
α ≤ᵖ β = V._≤ᵖ_ α β

≤ᶜ-refl {α} = elimProp {P = λ α → α ≤ᶜ α}
  (λ _ → isProp≤ᶜ) tt (λ ih → ih) (λ ih n → ∣ n , ih n ∣₁) α

≤ᶜs {α} = elimProp {P = λ α → α ≤ᶜ suc α}
  (λ _ → isProp≤ᶜ) tt (λ ih → ih) (λ ih n → ≤ᶜ-trans (ih n) f≤ᶜl) α

≤ᶜl {α} {f} {n} = elimProp {P = λ α → (f : MonoSeq) (n : ℕ) → α ≤ᶜ fst f n → α ≤ᶜ lim f}
  (λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isProp≤ᶜ)
  (λ _ _ _ → tt)
  (λ _ f n H → ∣ n , H ∣₁)
  (λ {e} IH f n H m → ∣ n , ≤ᶜ-trans (IH m e m ≤ᶜ-refl) H ∣₁)
  α f n
```

## Transitivity

Transitivity is **a single application of `elimProp`, nested three deep** — on the
*middle* ordinal `β`, then the first `α`, then the third `γ`. The body is *not*
recursive: it delegates to the already-terminating `elimProp`, whose induction
hypotheses arrive pre-unpacked, so the truncation `rec` inside only *selects* an
existing hypothesis index, never makes a fresh recursive call. The descent is the
**middle-first lexicographic** order `(β, α, γ)`, which strictly decreases in
every clause of the original recursive definition. All `l≡l`/`isSetOrd` path cases
of `α`, `β`, `γ` are discharged automatically by the three nested `elimProp`s.

```agda
≤ᶜ-trans {α} {β} {γ} H₁ H₂ = elimProp {P = P} Pprop Pz Ps Pl β α H₁ γ H₂
  where
  P : Ord → Type
  P β = (α : Ord) → α ≤ᶜ β → (γ : Ord) → β ≤ᶜ γ → α ≤ᶜ γ

  Pprop : ∀ β → isProp (P β)
  Pprop β = isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isProp≤ᶜ

  Pz : P zero
  Pz α = elimProp {P = Q} Qprop (λ _ _ H → H) (λ _ H _ _ → ⊥-rec H) (λ _ H _ _ → ⊥-rec H) α
    where
    Q : Ord → Type
    Q α = α ≤ᶜ zero → (γ : Ord) → zero ≤ᶜ γ → α ≤ᶜ γ
    Qprop : ∀ α → isProp (Q α)
    Qprop α = isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isProp≤ᶜ

  Ps : ∀ {β} → P β → P (suc β)
  Ps {β} IHβ α = elimProp {P = Q} Qprop Qz Qs Ql α
    where
    Q : Ord → Type
    Q α = α ≤ᶜ suc β → (γ : Ord) → suc β ≤ᶜ γ → α ≤ᶜ γ
    Qprop : ∀ α → isProp (Q α)
    Qprop α = isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isProp≤ᶜ
    Qz : Q zero
    Qz _ _ _ = tt
    Qs : ∀ {α} → Q α → Q (suc α)
    Qs {α} _ H₁ γ = elimProp {P = R} Rprop (λ K → ⊥-rec K) Rs Rl γ
      where
      R : Ord → Type
      R γ = suc β ≤ᶜ γ → suc α ≤ᶜ γ
      Rprop : ∀ γ → isProp (R γ)
      Rprop γ = isPropΠ λ _ → isProp≤ᶜ
      Rs : ∀ {γ} → R γ → R (suc γ)
      Rs {γ} _ K = IHβ α H₁ γ K
      Rl : ∀ {g} → (∀ n → R (fst g n)) → R (lim g)
      Rl {g} IHg K = rec squash₁ (λ { (m , h) → ∣ (m , IHg m h) ∣₁ }) K
    Ql : ∀ {e} → (∀ n → Q (fst e n)) → Q (lim e)
    Ql {e} IHe H₁ γ = elimProp {P = R} Rprop (λ K → ⊥-rec K) Rs Rl γ
      where
      R : Ord → Type
      R γ = suc β ≤ᶜ γ → lim e ≤ᶜ γ
      Rprop : ∀ γ → isProp (R γ)
      Rprop γ = isPropΠ λ _ → isProp≤ᶜ
      Rs : ∀ {γ} → R γ → R (suc γ)
      Rs {γ} _ K n = IHe n (H₁ n) (suc γ) K
      Rl : ∀ {g} → (∀ n → R (fst g n)) → R (lim g)
      Rl {g} _ K n = rec squash₁ (λ { (m , h) → ∣ (m , IHe n (H₁ n) (fst g m) h) ∣₁ }) K

  Pl : ∀ {f} → (∀ n → P (fst f n)) → P (lim f)
  Pl {f} IHf α = elimProp {P = Q} Qprop Qz Qs Ql α
    where
    Q : Ord → Type
    Q α = α ≤ᶜ lim f → (γ : Ord) → lim f ≤ᶜ γ → α ≤ᶜ γ
    Qprop : ∀ α → isProp (Q α)
    Qprop α = isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isProp≤ᶜ
    Qz : Q zero
    Qz _ _ _ = tt
    Qs : ∀ {α} → Q α → Q (suc α)
    Qs {α} _ H₁ γ = elimProp {P = R} Rprop (λ K → ⊥-rec K) Rs Rl γ
      where
      R : Ord → Type
      R γ = lim f ≤ᶜ γ → suc α ≤ᶜ γ
      Rprop : ∀ γ → isProp (R γ)
      Rprop γ = isPropΠ λ _ → isProp≤ᶜ
      Rs : ∀ {γ} → R γ → R (suc γ)
      Rs {γ} _ K = rec isProp≤ᶜ (λ { (n , h) → IHf n (suc α) h (suc γ) (K n) }) H₁
      Rl : ∀ {g} → (∀ n → R (fst g n)) → R (lim g)
      Rl {g} _ K = rec squash₁
        (λ { (n , h) → rec squash₁ (λ { (m , h') → ∣ (m , IHf n (suc α) h (fst g m) h') ∣₁ }) (K n) }) H₁
    Ql : ∀ {e} → (∀ n → Q (fst e n)) → Q (lim e)
    Ql {e} _ H₁ γ = elimProp {P = R} Rprop (λ K → ⊥-rec K) Rs Rl γ
      where
      R : Ord → Type
      R γ = lim f ≤ᶜ γ → lim e ≤ᶜ γ
      Rprop : ∀ γ → isProp (R γ)
      Rprop γ = isPropΠ λ _ → isProp≤ᶜ
      Rs : ∀ {γ} → R γ → R (suc γ)
      Rs {γ} _ K n = rec isProp≤ᶜ (λ { (m , h) → IHf m (fst e n) h (suc γ) (K m) }) (H₁ n)
      Rl : ∀ {g} → (∀ n → R (fst g n)) → R (lim g)
      Rl {g} _ K n = rec squash₁
        (λ { (m , h) → rec squash₁ (λ { (k , h') → ∣ (k , IHf m (fst e n) h (fst g k) h') ∣₁ }) (K m) }) (H₁ n)
```

## Soundness

`encode≤` is a single application of `≤-elimProp` (recursion on the `_≤_`
derivation), hence non-recursive; the `l≡l`/`isSetOrd`/`isProp≤` cases are
discharged automatically. The hard `l≤` method uses `≤-elimProp`'s second
hypothesis `H₂ : ∀ n → suc (f n) ≤ᶜ f (suc n)` (the sequence's monotonicity), and
an inner `elimProp` on the bound `α`. The explicit type ascriptions in the limit
case are the performance pin described above.

```agda
encode≤ = ≤-elimProp {P = λ {α} {β} _ → α ≤ᶜ β}
  (λ _ → isProp≤ᶜ)
  tt
  (λ _ ih → ih)
  (λ _ ih → ≤ᶜl ih)
  l≤-case
  (λ ih₁ ih₂ → ≤ᶜ-trans ih₁ ih₂)
  where
  l≤-case : ∀ {f α} (f≤α : ∀ n → f [ n ] ≤ α) →
            (∀ n → f [ n ] ≤ᶜ α) → (∀ n → suc (f [ n ]) ≤ᶜ f [ ℕ.suc n ]) → lim f ≤ᶜ α
  l≤-case {f} {α} _ H₁ H₂ = elimProp {P = Q} Qprop Qz (λ _ H → H) Ql α H₁
    where
    Q : Ord → Type
    Q α = (∀ n → fst f n ≤ᶜ α) → lim f ≤ᶜ α
    Qprop : ∀ α → isProp (Q α)
    Qprop α = isPropΠ λ _ → isProp≤ᶜ
    Qz : Q zero
    Qz H₁ = ⊥-rec absurd
      where
      -- pin the reduction `suc (fst f 0) ≤ᶜ zero ↝ ⊥` via an explicit type
      -- ascription, so the *conversion checker* (not the lossy unifier) runs it.
      absurd : ⊥
      absurd = ≤ᶜ-trans {suc (f [ 0 ])} {f [ 1 ]} {zero} (H₂ 0) (H₁ 1)
    Ql : ∀ {g} → (∀ n → Q (fst g n)) → Q (lim g)
    Ql {g} _ H₁ n = result
      where
      step : ∃[ m ∈ ℕ ] suc (fst f n) ≤ᶜ fst g m
      step = ≤ᶜ-trans {suc (f [ n ])} {f [ ℕ.suc n ]} {lim g} (H₂ n) (H₁ (ℕ.suc n))
      -- Every type below is ascribed explicitly so Agda need not *infer* implicit
      -- arguments by unifying against the giant elim-unfolded `≤ᶜ` terms.
      combine : Σ[ m ∈ ℕ ] suc (fst f n) ≤ᶜ fst g m → ∃[ m ∈ ℕ ] fst f n ≤ᶜ fst g m
      combine (m , H) = ∣ m , ≤ᶜ-trans {fst f n} {suc (fst f n)} {fst g m} ≤ᶜs H ∣₁
      result : ∃[ m ∈ ℕ ] fst f n ≤ᶜ fst g m
      result = rec squash₁ combine step
```
