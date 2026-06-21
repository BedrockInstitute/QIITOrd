<!-- SPDX-License-Identifier: AGPL-3.0-only -->
# Constructor analysis and properties of the order

This module collects the elementary consequences of the QIIT definition that do
*not* require the recursive order-code of `QIITOrd.Order.Code`: telling the
constructors apart, inverting them where possible, and the basic theory of the
strict order `_<_`. Everything here is a direct application of `elimProp` /
`≤-elimProp` or of the order constructors.

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module QIITOrd.Properties where
open import QIITOrd.Base

open import Cubical.Foundations.Prelude hiding (≡⟨⟩-syntax; _∎)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty as ⊥ using (⊥; isProp⊥)
open import Cubical.Data.Unit
open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; rec)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open BinaryRelation using (isTrans')
```

## Distinguishing the constructors

Since `Ord` is a set, "being `zero`" is a proposition, computed by recursion as
`Unit` at `zero` and `⊥` elsewhere (the path/set constructors are handled by
`isSet→SquareP`). From `isZero` we immediately get that `zero` is distinct from
any successor or limit.

```agda
isZeroₚ : Ord → hProp ℓ-zero
isZeroₚ zero = Unit , isPropUnit
isZeroₚ (suc _) = ⊥ , isProp⊥
isZeroₚ (lim _) = ⊥ , isProp⊥
isZeroₚ (l≡l _ _) = ⊥ , isProp⊥
isZeroₚ (isSetOrd _ _ p q i j) =
  isSet→SquareP (λ _ _ → isSetHProp)
    (λ i → isZeroₚ (p i))
    (λ i → isZeroₚ (q i)) refl refl i j

isZero : Ord → Type
isZero α = typ (isZeroₚ α)

isPropIsZero : isProp (isZero α)
isPropIsZero {α} = str (isZeroₚ α)

z≢s : zero ≢ suc α
z≢s z≡sx = subst isZero z≡sx tt

z≢l : zero ≢ lim f
z≢l z≡l = subst isZero z≡l tt
```

Conversely, anything satisfying `isZero` *is* `zero` (by `elimProp`), and via the
monotonicity of `isZero` along `_≤_` (by `≤-elimProp`) we get that the only
ordinal `≤ zero` is `zero` itself.

```agda
decodeZero : isZero α → α ≡ zero
decodeZero = elimProp {P = λ α → isZero α → α ≡ zero}
  (λ _ → isProp→ $ isSetOrd _ _)
  (λ _ → refl) (λ _ ()) (λ _ ()) _

≤Zero→isZero : α ≤ β → isZero β → isZero α
≤Zero→isZero {α} {β} = ≤-elimProp (λ _ → isProp→ $ isPropIsZero)
  (λ _ → tt) (λ _ _ ()) (λ _ _ ())
  (λ f≤α ih₁ ih₂ isZ → ih₂ 0 (ih₁ 1 isZ))
  λ ih₁ ih₂ → ih₁ ∘ ih₂

≤z→≡z : α ≤ zero → α ≡ zero
≤z→≡z ≤z = decodeZero $ ≤Zero→isZero ≤z tt
```

The same pattern identifies successors, giving `suc α ≢ lim f`.

```agda
isSucₚ : Ord → hProp ℓ-zero
isSucₚ zero = ⊥ , isProp⊥
isSucₚ (suc _) = Unit , isPropUnit
isSucₚ (lim _) = ⊥ , isProp⊥
isSucₚ (l≡l _ _) = ⊥ , isProp⊥
isSucₚ (isSetOrd _ _ p q i j) =
  isSet→SquareP (λ i j → isSetHProp)
    (λ i → isSucₚ (p i))
    (λ i → isSucₚ (q i)) refl refl i j

isSuc : Ord → Type
isSuc α = typ (isSucₚ α)

isPropIsSuc : isProp (isSuc α)
isPropIsSuc {α} = str (isSucₚ α)

s≢l : suc α ≢ lim f
s≢l s≡l = subst isSuc s≡l tt
```

## Order exclusions at `zero`

A successor is never `≤ zero` — proved by induction on the derivation, peeling off
`≤-trans` and `l≤` and using the distinctness facts above. Hence a limit is not
`≤ zero` either (its first element would be), and so nothing is `< zero`.

```agda
s≰z : suc α ≰ zero
s≰z s≤z = aux s≤z refl tt where
  aux : β ≤ γ → β ≡ suc α → ¬ isZero γ
  aux z≤     z≡s _ = z≢s z≡s
  aux (l≤ _) l≡s _ = s≢l $ sym l≡s
  aux (≤-trans β≤δ δ≤γ) β≡sα isZγ = aux β≤δ β≡sα $ ≤Zero→isZero δ≤γ isZγ
  aux (isProp≤ p q i) β≡sα isZγ = isProp⊥ (aux p β≡sα isZγ) (aux q β≡sα isZγ) i

l≰z : lim f ≰ zero
l≰z {f} l≤z = s≰z $
  suc (f [ 0 ]) ≤⟨ snd f 0 ⟩
  f [ 1 ]       ≤⟨ f≤l ⟩
  lim f         ≤⟨ l≤z ⟩
  zero          ≤∎

≮z : α ≮ zero
≮z = s≰z

>z→≢z : α > zero → α ≢ zero
>z→≢z >z ≡z = ≮z $ subst (_ <_) ≡z >z
```

## Predecessor and injectivity of `suc`

`pred` is defined by direct pattern matching (it is the identity on `zero` and
limits, and strips one `suc`). From it, `suc` is injective, `pred α ≤ α`, and —
most usefully — `pred` is monotone, which yields the inversion `s≤s-inv` of the
successor-monotonicity constructor and the fact that `lim f ≤ suc α` already
gives `lim f ≤ α`.

```agda
pred : Ord → Ord
pred zero = zero
pred (suc α) = α
pred (lim f) = lim f
pred (l≡l {f} {g} f≈g i) = l≡l {f} {g} f≈g i
pred (isSetOrd α β p q i j) = isSetOrd (pred α) (pred β) (cong pred p) (cong pred q) i j

suc-inj : suc α ≡ suc β → α ≡ β
suc-inj = cong pred

p≤ : pred α ≤ α
p≤ = elimProp (λ α → isProp≤ {pred α} {α}) z≤ (λ _ → ≤s) (λ _ → ≤-refl) _

p≤p : α ≤ β → pred α ≤ pred β
p≤p = ≤-elimProp (λ _ → isProp≤)
  z≤ (λ α≤β _ → α≤β) (λ α≤f _ → ≤-trans p≤ $ ≤l α≤f)
  (λ {f} {α} _ H₁ H₂ → l≤ λ n →
    f [ n ]               ≤⟨ H₂ n ⟩
    pred (f [ ℕ.suc n ])  ≤⟨ H₁ (ℕ.suc n) ⟩
    pred α                ≤∎)
  ≤-trans

s≤s-inv : suc α ≤ suc β → α ≤ β
s≤s-inv = p≤p

s<s-inv : α < suc β → α ≤ β
s<s-inv = s≤s-inv

l≤s⇒l≤ : lim f ≤ suc α → lim f ≤ α
l≤s⇒l≤ {f} {α} l≤s = l≤ λ n → s≤s-inv $
  f [ n ]       <⟨ snd f n ⟩
  f [ ℕ.suc n ] ≤⟨ l≤-inv l≤s _ ⟩
  suc α         ≤∎
```

## The strict order

`α < β` is `suc α ≤ β`. It is propositional, irreflexively below its own
successor, monotone, and `zero < suc α`. Strict order implies non-strict, and the
two compose with `_≤_` on either side. We name the mixed-transitivity statements
directly (the cubical library has no heterogeneous `Trans` combinator).

```agda
isProp< : isProp (α < β)
isProp< = isProp≤

<s : α < suc α
<s = ≤-refl

s<s : α < β → suc α < suc β
s<s = s≤s

z<s : zero < suc α
z<s = s≤s z≤

<⇒≤ : α < β → α ≤ β
<⇒≤ α<β = ≤-trans ≤s α<β

<-trans : isTrans' _<_
<-trans α<β β<γ = ≤-trans α<β (<⇒≤ β<γ)

<-≤-trans : α < β → β ≤ γ → α < γ
<-≤-trans = ≤-trans

≤-<-trans : α ≤ β → β < γ → α < γ
≤-<-trans = ≤-trans ∘ s≤s
```

## Properties involving limits

`l≤l` lifts a cofinality `fst f ≼ fst g` to `lim f ≤ lim g`; pointwise-equal
sequences have equal limits; dropping the first element of a sequence does not
change its limit. The remaining lemmas record where `zero`, `one`, and the
sequence elements sit strictly below a limit, culminating in the characterisations
of the ordinals that are `> zero` (exactly the non-`zero` ones) and `> one`.

```agda
l≤l : fst f ≼ fst g → lim f ≤ lim g
l≤l f≼g = l≤ λ n → rec isProp≤ (λ H → ≤-trans (snd H) f≤l) (f≼g n)

l≡l-pointwise : (∀ n → f [ n ] ≡ g [ n ]) → lim f ≡ lim g
l≡l-pointwise eq = l≡l $ (λ n → ∣ n , ≡⇒≤ (eq n) ∣₁) , (λ n → ∣ n , ≡⇒≤ (sym $ eq n) ∣₁)

dropFirst : MonoSeq → MonoSeq
dropFirst f = fst f ∘ ℕ.suc , snd f ∘ ℕ.suc

l≡l₁ : lim f ≡ lim (dropFirst f)
l≡l₁ {f} = l≡l $ (λ n → ∣ n , <⇒≤ (snd f n) ∣₁) , (λ n → ∣ ℕ.suc n , ≤-refl ∣₁)

≤f→≤l : α ≤ f [ n ] → α ≤ lim f
≤f→≤l a≤f = ≤-trans a≤f f≤l

<f→<l : α < f [ n ] → α < lim f
<f→<l a<f = ≤-trans a<f f≤l

z<l : zero < lim f
z<l {f = f} =
  zero    <⟨ z<s ⟩suc
  f [ 0 ] <⟨ snd f 0 ⟩
  f [ 1 ] ≤⟨ f≤l ⟩
  lim f   ≤∎

f<l : f [ n ] < lim f
f<l {f} = ≤-trans (snd f _) f≤l

1<l : one < lim f
1<l {f = f} =
  one           <⟨ s<s z<s ⟩suc
  suc (f [ 0 ]) <⟨ s≤s (snd f 0) ⟩
  suc (f [ 1 ]) ≤⟨ f<l ⟩
  lim f         ≤∎

≢z→>z : α ≢ zero → α > zero
≢z→>z = elimProp {P = λ α → α ≢ zero → α > zero} (λ _ → isProp→ isProp≤)
  (λ z≢z → ⊥.rec $ z≢z refl) (λ _ _ → z<s) (λ _ _ → z<l) _

≢z→≢1→>1 : α ≢ zero → α ≢ one → α > one
≢z→≢1→>1 = elimProp {P = λ α → α ≢ zero → α ≢ one → α > one}
  (λ _ → isProp→ $ isProp→ isProp≤)
  (λ z≢z _ → ⊥.rec $ z≢z refl)
  (λ _ _ s≢1 → s≤s $ ≢z→>z $ s≢1 ∘ cong suc)
  (λ _ _ _ → 1<l) _
```
