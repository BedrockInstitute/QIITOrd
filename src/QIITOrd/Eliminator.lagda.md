<!-- SPDX-License-Identifier: AGPL-3.0-only -->
# The dependent eliminator

`QIITOrd.Base` exports `elimProp`/`≤-elimProp`, which eliminate into
*propositions*. To define data that is not proof-irrelevant — in particular the
order-code `_≤ᵖ_`, whose values live in `hProp` (a **set**, not a proposition) —
we need the **general dependent eliminator**, where the path constructors
`l≡l`/`isSetOrd` must be discharged *by hand* via the user-supplied coherence
data.

This module packages that eliminator as a sequence of nested module parameters,
so that defining a function `Ord → T` (and a proof that it respects `_≤_`) amounts
to filling in a fixed checklist of methods. It is parameterised by two universe
levels.

```agda
{-# OPTIONS --cubical --safe #-}

module QIITOrd.Eliminator ℓ ℓ' where
open import QIITOrd.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec)
```

A **target** is a family `T : Ord → Type` we are eliminating into, together with
a relation `≦` over it indexed by `_≤_` — read `Tα ≦⟨ α≤β ⟩ Tβ` as "`Tα` sits
below `Tβ`, witnessed by `α≤β`". The eliminator produces both a section of `T`
and a proof that it is monotone for `≦`.

```agda
Target : Type _
Target = Ord → Type ℓ

≤Target : Target → Type _
≤Target T = {α β : Ord} → α ≤ β → T α → T β → Type ℓ'
```

## The method checklist

Inside `Targeting T ≦` we name the pieces the eliminator will consume. `IsSetT`
and `IsProp≦` are the truncation levels; `Initial`/`Successor` interpret `zero`
and `suc`.

```agda
module Targeting (T : Target) (≦ : ≤Target T) where

  ≦-syntax = ≦
  syntax ≦-syntax α≤β Tα Tβ = Tα ≦⟨ α≤β ⟩ Tβ

  IsSetT : Type _
  IsSetT = ∀ α → isSet (T α)

  IsProp≦ : Type _
  IsProp≦ = ∀ {α β} (α≤β : α ≤ β) {Tα : T α} {Tβ : T β} → isProp (Tα ≦⟨ α≤β ⟩ Tβ)

  Initial : Type _
  Initial = T zero

  Successor : Type _
  Successor = ∀ {α} → T α → T (suc α)
```

To interpret `lim`, we need a `Map` of a monotone sequence: a choice of `T (f n)`
for each `n`, *coherent* with `succ` along the monotonicity witnesses. `Supremum`
takes such a `Map` to `T (lim f)`. The relations `_≾_` and `_≋_` lift `≦` and
bisimilarity to `Map`s, and `SupPath` is the coherence the `l≡l` constructor
demands: bisimilar maps have equal suprema, over the path `l≡l`.

```agda
  module SupremumStatement (succ : Successor) where

    Map : MonoSeq → Type _
    Map f = Σ[ F ∈ (∀ n → T (f [ n ])) ] ∀ n → succ (F n) ≦⟨ snd f n ⟩ F (suc n)

    Supremum : Type _
    Supremum = ∀ {f} → Map f → T (lim f)

    module _ {f g} where
      _≾⟨_⟩_ : Map f → ℕ → Map g → Type _
      F ≾⟨ n ⟩ G = ∃[ m ∈ ℕ ] Σ[ fn≤fm ∈ f [ n ] ≤ g [ m ] ] fst F n ≦⟨ fn≤fm ⟩ fst G m

      _≾_ : Map f → Map g → Type _
      F ≾ G = ∀ n → F ≾⟨ n ⟩ G

    module _ {f g} where
      _≋_ : Map f → Map g → Type _
      F ≋ G = F ≾ G × G ≾ F

    SupPath : Supremum → Type _
    SupPath sup = ∀ {f g} (f≈g : fst f ≈ fst g) (F : Map f) (G : Map g) →
      F ≋ G → PathP (λ i → T (l≡l {f} {g} f≈g i)) (sup F) (sup G)
```

## The monotonicity methods

Given the interpretations of the constructors (`init`, `succ`, `sup`, `supPath`),
`Assigning` lists the methods that make the section *monotone*: the order-code
analogues of `z≤`, `s≤s`, `≤l`, `l≤`, and `≤-trans`.

```agda
  open SupremumStatement using (Supremum; SupPath)
  module Assigning (init : Initial) (succ : Successor) (sup : Supremum succ) (supPath : SupPath succ sup) where
    open SupremumStatement succ using (Map; _≾_; _≾⟨_⟩_; _≋_)

    Minimality : Type _
    Minimality = ∀ {α} {Tα : T α} → init ≦⟨ z≤ ⟩ Tα

    Monotonicity : Type _
    Monotonicity = ∀ {α β} {α≤β : α ≤ β} {Tα : T α} {Tβ : T β} → Tα ≦⟨ α≤β ⟩ Tβ → succ Tα ≦⟨ s≤s α≤β ⟩ succ Tβ

    UpperBoundProperty : Type _
    UpperBoundProperty = ∀ {α f n} {α≤f : α ≤ f [ n ]} (F : Map f) (Tα : T α) →
      Tα ≦⟨ α≤f ⟩ fst F n → Tα ≦⟨ ≤l α≤f ⟩ sup F

    SupremumProperty : Type _
    SupremumProperty = ∀ {f α} {f≤α : ∀ n → f [ n ] ≤ α} (F : Map f) (Tα : T α) →
      (∀ n → fst F n ≦⟨ f≤α n ⟩ Tα) → sup F ≦⟨ l≤ f≤α ⟩ Tα

    Transitivity : Type _
    Transitivity = ∀ {α β γ} {α≤β : α ≤ β} {β≤γ : β ≤ γ} {Tα : T α} {Tβ : T β} {Tγ : T γ} →
      Tα ≦⟨ α≤β ⟩ Tβ → Tβ ≦⟨ β≤γ ⟩ Tγ → Tα ≦⟨ ≤-trans α≤β β≤γ ⟩ Tγ
```

## The eliminator itself

Once every method is supplied (`Satisfying`), the two mutually-recursive functions
`elim : (α : Ord) → T α` and `≤-elim : (α≤β : α ≤ β) → elim α ≦⟨ α≤β ⟩ elim β`
are defined by direct structural recursion. The `lim` case feeds the sequence's
elements and monotonicities into `sup`; the `l≡l` case is discharged by the
user's `supPath`, with the bisimilarity translated into a `_≋_` of maps; and
`isSetOrd`/`isProp≤` cases use the supplied truncation levels.

```agda
    module Satisfying
      (isSetT : IsSetT) (isProp≦ : IsProp≦) (ι≦ : Minimality) (s≦s : Monotonicity)
      (≦l : UpperBoundProperty) (l≦ : SupremumProperty) (≦-trans : Transitivity)
      where

      elim : (α : Ord) → T α
      ≤-elim : {α β : Ord} (α≤β : α ≤ β) → elim α ≦⟨ α≤β ⟩ elim β

      elim zero = init
      elim (suc α) = succ (elim α)
      elim (lim f) = sup (elim ∘ fst f , ≤-elim ∘ snd f)
      elim (l≡l {f} {g} f≈g i) = supPath f≈g F G (F≾G , G≾F) i where
        F = elim ∘ fst f , ≤-elim ∘ snd f
        G = elim ∘ fst g , ≤-elim ∘ snd g
        F≾G : F ≾ G
        F≾G n = aux n (fst f≈g n) where
          aux : ∀ n → fst f ≼⟨ n ⟩ fst g → F ≾⟨ n ⟩ G
          aux n ∣ m , fn≤gm ∣₁ = ∣ m , fn≤gm , ≤-elim fn≤gm ∣₁
          aux n (squash₁ p q i) = squash₁ (aux n p) (aux n q) i
        G≾F : G ≾ F
        G≾F n = aux n (snd f≈g n) where
          aux : ∀ n → fst g ≼⟨ n ⟩ fst f → G ≾⟨ n ⟩ F
          aux n ∣ m , gm≤fn ∣₁ = ∣ m , gm≤fn , ≤-elim gm≤fn ∣₁
          aux n (squash₁ p q i) = squash₁ (aux n p) (aux n q) i
      elim (isSetOrd α β p q i j) = isSet→SquareP
        (λ i j → isSetT $ isSetOrd α β p q i j)
        (λ i → elim (p i)) (λ i → elim (q i)) refl refl i j

      ≤-elim z≤ = ι≦
      ≤-elim (s≤s α≤β) = s≦s (≤-elim α≤β)
      ≤-elim (≤l {α} {f} α≤f) = ≦l (elim ∘ fst f , ≤-elim ∘ snd f) (elim α) (≤-elim α≤f)
      ≤-elim (l≤ {f} {β} f≤β) = l≦ (elim ∘ fst f , ≤-elim ∘ snd f) (elim β) (≤-elim ∘ f≤β)
      ≤-elim (≤-trans α≤β β≤γ) = ≦-trans (≤-elim α≤β) (≤-elim β≤γ)
      ≤-elim (isProp≤ α≤β β≤γ i) = isProp→PathP
        (λ i → isProp≦ $ isProp≤ α≤β β≤γ i)
        (≤-elim α≤β) (≤-elim β≤γ) i
```
