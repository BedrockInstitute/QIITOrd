<!-- SPDX-License-Identifier: AGPL-3.0-only -->
# The non-dependent eliminator

When the target family `T α` does not actually depend on `α` — i.e. we are
defining a *function* `Ord → A` into a fixed type `A`, ordered by a fixed
relation `_≦_` — the dependent eliminator of `QIITOrd.Eliminator` specialises to a
much shorter checklist. This module performs that specialisation once and for
all: it instantiates the dependent `Targeting (λ _ → A) (λ _ → _≦_)` and exposes
the simplified `elim`/`≤-elim`.

This is the form used to build the order-code `_≤ᵖ_` in `QIITOrd.Order.Code.Base`
(there, `A` is the type of monotone `hProp`-valued predicates, and `_≦_` is
up-set inclusion).

```agda
{-# OPTIONS --cubical --safe #-}

module QIITOrd.Eliminator.NonDependent ℓ ℓ' where
open import QIITOrd.Base
import QIITOrd.Eliminator ℓ ℓ' as Dep

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec)
```

Fixing `A` and `_≦_`, a `Supremum` is just a map `Mapped → A` from `≦`-increasing
sequences, and `SupPath` is the non-indexed coherence "bisimilar sequences have
equal suprema" — the dependent `PathP` collapses to an ordinary `≡` because the
codomain no longer varies along `l≡l`.

```agda
module Targeting
  (A : Type ℓ)
  (_≦_ : A → A → Type ℓ')
  where

  module DepTarget = Dep.Targeting (λ _ → A) (λ _ → _≦_)
  open Bisimulation _≦_ renaming (_≈_ to _≋_)

  module SupremumStatement (succ : A → A) where
    open MonotonicSequence succ _≦_ renaming (MonoSeq to Mapped)

    Supremum : Type _
    Supremum = Mapped → A

    SupPath : Supremum → Type _
    SupPath sup = ∀ (F G : Mapped) → fst F ≋ fst G → sup F ≡ sup G
```

Supplying `ι`, `succ`, `sup`, `supPath` we obtain `Assigning`, which forwards to
the dependent `Assigning` after repackaging bisimilarity into the dependent
`_≾_`-form. The remaining methods (`ι≦`, `s≦s`, `≦l`, `l≦`, `≦-trans`) are then
exactly the order axioms one expects, with no indexing.

```agda
  open SupremumStatement using (Supremum; SupPath)
  module Assigning
    (ι : A)
    (succ : A → A)
    (sup : Supremum succ)
    (supPath : SupPath succ sup)
    where

    module DepAssign = DepTarget.Assigning ι succ sup
      (λ { f≈g F G (F≾G , G≾F) → supPath F G $
        (λ n → rec squash₁ (λ { (m , _ , H) → ∣ m , H ∣₁ }) (F≾G n)) ,
        (λ n → rec squash₁ (λ { (m , _ , H) → ∣ m , H ∣₁ }) (G≾F n))
      })

    module Satisfying
      (isSetA : isSet A)
      (isProp≦ : ∀ {x y} → isProp (x ≦ y))
      (ι≦ : ∀ {x} → ι ≦ x)
      (s≦s : ∀ {x y} → x ≦ y → succ x ≦ succ y)
      (≦l : ∀ {n} F x → (x ≦ fst F n) → x ≦ sup F)
      (l≦ : ∀ F x → (∀ n → fst F n ≦ x) → sup F ≦ x)
      (≦-trans : ∀ {x y z} → x ≦ y → y ≦ z → x ≦ z)
      where

      module DepElim = DepAssign.Satisfying (λ _ → isSetA) (λ _ → isProp≦) ι≦ s≦s ≦l l≦ ≦-trans

      elim : Ord → A
      elim = DepElim.elim

      ≤-elim : α ≤ β → elim α ≦ elim β
      ≤-elim = DepElim.≤-elim
```
