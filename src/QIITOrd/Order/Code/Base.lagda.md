<!-- SPDX-License-Identifier: AGPL-3.0-only -->
# The order-code, via the external eliminator

This module defines the **order-code** `_≤ᵖ_ : Ord → Ord → hProp` — a recursive,
*computing* characterisation of `_≤_` — as a single application of the external
eliminator of `QIITOrd.Eliminator.NonDependent`. This is the construction that
**eliminates `{-# TERMINATING #-}`**: rather than defining `_≤ᵖ_` by direct
double recursion (which Agda cannot see terminating, because its two-argument
recursion re-enters itself at cross positions), we recurse on the *first* ordinal
through an eliminator that was already proved terminating in `QIITOrd.Eliminator`.
Since `α ≤ᵖ β = fst (elim α) β` is then **non-recursive**, there is no recursion
for the termination checker to reject.

The full story — why the naive definition fails, and why routing through an
external recursor dissolves it — is in [`docs/termination.md`](../../../../docs/termination.md);
this module is its concrete realisation, faithful to the "work in progress" the
[reference paper](https://arxiv.org/abs/2208.03844) left open.

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}
module QIITOrd.Order.Code.Base where

open import QIITOrd.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty using (⊥; isProp⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec)
```

## The carrier of the eliminator

We eliminate `Ord` into the type `A` of **monotone `hProp`-valued predicates**:
each `P : Ord → hProp` paired with a proof that `typ ∘ P` respects `_≤_`. The
monotonicity is essential — the second-argument coherence `lim f ≤ᵖ l≡l …` needs
it and the bare function `Ord → hProp` does not carry it. The order `_≦_` on `A`
is **up-set inclusion**: `x ≦ y` iff everything above `y` is above `x`. It is
written with projections (not pattern matching) so that it reduces on variables.

```agda
-- A monotone hProp-valued predicate on ordinals.
Mono : (Ord → hProp ℓ-zero) → Type
Mono P = ∀ {x y} → x ≤ y → typ (P x) → typ (P y)

isPropMono : ∀ P → isProp (Mono P)
isPropMono P = isPropImplicitΠ2 λ x y → isPropΠ λ _ → isPropΠ λ _ → str (P y)

A : Type₁
A = Σ[ P ∈ (Ord → hProp ℓ-zero) ] Mono P

-- "up-set inclusion": x ≦ y iff y's up-set ⊆ x's up-set.  Defined with
-- projections (not pattern matching) so it reduces on variables, e.g. `ι ≦ x`.
_≦_ : A → A → Type
x ≦ y = ∀ γ → typ (fst y γ) → typ (fst x γ)

isProp≦ : ∀ {x y} → isProp (x ≦ y)
isProp≦ {x} = isPropΠ λ γ → isPropΠ λ _ → str (fst x γ)

isSetA : isSet A
isSetA = isSetΣ (isSetΠ λ _ → isSetHProp) λ P → isProp→isSet (isPropMono P)
```

We instantiate the non-dependent eliminator at this `A`/`_≦_`. The `zero` case is
the always-true predicate `ι` (`Unit` everywhere), which is trivially `≦`-above
everything; `≦`-transitivity is composition.

```agda
import QIITOrd.Eliminator (ℓ-suc ℓ-zero) ℓ-zero as SD
open import QIITOrd.Eliminator.NonDependent (ℓ-suc ℓ-zero) ℓ-zero
open Targeting A _≦_

ι : A
ι = (λ _ → Unit , isPropUnit) , (λ _ _ → tt)

≦-trans : ∀ {x y z} → x ≦ y → y ≦ z → x ≦ z
≦-trans h₁ h₂ γ = h₁ γ ∘ h₂ γ
```

## The successor method

`succ` sends `α ≤ᵖ_` to `suc α ≤ᵖ_`. Its function part is an **inner**
`SD.elim` recursion on the *second* ordinal `β` (so even this nested recursion
lives inside an external eliminator), and its monotonicity is that inner
eliminator's own `≤-elim`. The inner relation `≦ᵇ X Y = typ X → typ Y` is exactly
what makes `≤-elim` deliver the monotonicity the bundle needs, and what the inner
`supPath` (β's `l≡l` coherence) supports.

```agda
-- `succ (α ≤ᵖ_ , monoP) = (suc α ≤ᵖ_ , its monotonicity)`.
succ : A → A
succ (P , monoP) = elimᵇ , ≤-elimᵇ
  where
  module IT = SD.Targeting (λ (_ : Ord) → hProp ℓ-zero) (λ {_ _} _ Px Py → typ Px → typ Py)

  ιᵇ : IT.Initial
  ιᵇ = ⊥ , isProp⊥

  succᵇ : IT.Successor
  succᵇ {β'} _ = P β'             -- suc α ≤ᵖ suc β' = α ≤ᵖ β'

  module IA = IT.Assigning ιᵇ succᵇ
    (λ Fᵇ → (∃[ n ∈ ℕ ] typ (fst Fᵇ n)) , squash₁)       -- suc α ≤ᵖ lim f
    (λ { f≈g F G (F≾G , G≾F) → Σ≡Prop (λ _ → isPropIsProp)
        (hPropExt squash₁ squash₁
          (rec squash₁ (λ { (n , H) → rec squash₁ (λ { (m , _ , impl) → ∣ m , impl H ∣₁ }) (F≾G n) }))
          (rec squash₁ (λ { (n , H) → rec squash₁ (λ { (m , _ , impl) → ∣ m , impl H ∣₁ }) (G≾F n) }))) })

  module IS = IA.Satisfying
    (λ _ → isSetHProp)
    (λ {_} {_} _ {_} {Py} → isPropΠ λ _ → str Py)
    (λ {_} {_} → ⊥-rec)
    (λ {_} {_} {x≤y} _ → monoP x≤y)
    (λ { {_} {_} {n} _ _ h H → ∣ n , h H ∣₁ })
    (λ { _ Tα hs → rec (str Tα) (λ { (n , H) → hs n H }) })
    (λ h₁ h₂ → h₂ ∘ h₁)

  elimᵇ : Ord → hProp ℓ-zero
  elimᵇ = IS.elim
  ≤-elimᵇ : Mono elimᵇ
  ≤-elimᵇ = IS.≤-elim
```

## The supremum method

`sup` sends a `≦`-increasing sequence `F` of predicates `α'ₙ ≤ᵖ_` to
`lim α' ≤ᵖ_`. Its function part `P` is built *directly* from the outer sequence
(it does not self-recurse on `β`, except `isSetOrd`, structurally). The subtle
half is its monotonicity `mono`: pushing a *limit* element `α'ⱼ` below `lim w`
would look circular, but is obtained **without** transitivity by using the
sequence's *strict* monotonicity `Fmono : suc α'ⱼ ≤ α'ⱼ₊₁` to bump to the
existential form `suc α'ⱼ ≤ᶜ lim w`, then stripping the `suc` back off with the
per-element monotonicity `snd (F j)` (the helper `s≤ᶜ→`). Inversion (`inv`) and
the supremum bound (`bound`) are each a single `elimProp` on the ordinal.

```agda
-- the type of `≦`-increasing sequences of `A`-values (= `Mapped`).
module MS = MonotonicSequence succ _≦_
module BS = Bisimulation _≦_

module _ (FF : MS.MonoSeq) where
  private
    F     = fst FF
    Fmono = snd FF
    -- strip a `suc` off the j-th predicate, using its monotonicity `snd (F j)`.
    s≤ᶜ→ : ∀ j w → typ (fst (succ (F j)) w) → typ (fst (F j) w)
    s≤ᶜ→ j = elimProp {P = λ w → typ (fst (succ (F j)) w) → typ (fst (F j) w)}
      (λ w → isPropΠ λ _ → str (fst (F j) w))
      (λ H → ⊥-rec H)
      (λ _ H → snd (F j) ≤s H)
      (λ {v} ih → rec (str (fst (F j) (lim v))) (λ { (k , H) → snd (F j) f≤l (ih k H) }))

  P : Ord → hProp ℓ-zero
  P zero = ⊥ , isProp⊥
  P (suc z) = (∀ j → typ (fst (F j) (suc z))) , isPropΠ (λ j → str (fst (F j) (suc z)))
  P (lim f) = (∀ j → ∃[ m ∈ ℕ ] typ (fst (F j) (fst f m))) , isPropΠ (λ _ → squash₁)
  P (l≡l {f} {g} (f≼g , g≼f) i) = Σ≡Prop (λ _ → isPropIsProp)
    {u = (∀ j → ∃[ m ∈ ℕ ] typ (fst (F j) (fst f m))) , isPropΠ (λ _ → squash₁)}
    {v = (∀ j → ∃[ m ∈ ℕ ] typ (fst (F j) (fst g m))) , isPropΠ (λ _ → squash₁)}
    (hPropExt (isPropΠ λ _ → squash₁) (isPropΠ λ _ → squash₁)
      (λ H j → rec squash₁ (λ { (m , Hm) → rec squash₁ (λ { (k , fm≤gk) → ∣ k , snd (F j) fm≤gk Hm ∣₁ }) (f≼g m) }) (H j))
      (λ H j → rec squash₁ (λ { (m , Hm) → rec squash₁ (λ { (k , gm≤fk) → ∣ k , snd (F j) gm≤fk Hm ∣₁ }) (g≼f m) }) (H j)))
    i
  P (isSetOrd x y p q i j) = isSet→SquareP (λ _ _ → isSetHProp)
    (λ i → P (p i)) (λ i → P (q i)) refl refl i j

  -- `lim α' ≤ᶜ w → ∀ j. α'ⱼ ≤ᶜ w`   (l≤-inversion for the supremum)
  inv : ∀ w → typ (P w) → ∀ j → typ (fst (F j) w)
  inv = elimProp {P = λ w → typ (P w) → ∀ j → typ (fst (F j) w)}
    (λ w → isPropΠ λ _ → isPropΠ λ j → str (fst (F j) w))
    (λ H → ⊥-rec H)
    (λ _ H → H)
    (λ {v} _ H j → rec (str (fst (F j) (lim v))) (λ { (k , Hk) → snd (F j) f≤l Hk }) (H j))

  -- `(∀ j. α'ⱼ ≤ᶜ w) → lim α' ≤ᶜ w`  (the supremum property; uses `Fmono`)
  bound : ∀ w → (∀ j → typ (fst (F j) w)) → typ (P w)
  bound = elimProp {P = λ w → (∀ j → typ (fst (F j) w)) → typ (P w)}
    (λ w → isPropΠ λ _ → str (P w))
    (λ H → Fmono 0 zero (H 1))
    (λ _ H → H)
    (λ {v} _ H j → rec squash₁ (λ { (m , Hm) → ∣ m , s≤ᶜ→ j (fst v m) Hm ∣₁ }) (Fmono j (lim v) (H (ℕ.suc j))))

  mono : Mono P
  mono {x} {y} x≤y H = bound y (λ j → snd (F j) x≤y (inv x H j))

  sup-A : A
  sup-A = P , mono
```

## The two `l≡l` coherences and the order

`supPath` is the *first*-argument `l≡l` coherence: bisimilar `α'`-sequences give
the *same* predicate `lim α' ≤ᵖ_`. It is a path of functions `Ord → hProp`, given
pointwise by `elimProp` on `γ` (a proposition, since `hProp` is a set). With `ι`,
`succ`, `sup-A`, `supPath` in hand we open `Assigning`, prove the three outer
order methods (`s≦s`, `≦l`, `l≦` — each an `elimProp` on `γ`, or `inv`/`bound`),
and `open Satisfying` to obtain `elim`.

```agda
-- first-argument `l≡l` coherence: bisimilar α'-sequences give equal `lim α' ≤ᵖ_`.
supPath : ∀ (FF GG : MS.MonoSeq) → BS._≈_ (fst FF) (fst GG) → sup-A FF ≡ sup-A GG
supPath FF GG (F≼G , G≼F) = Σ≡Prop isPropMono (funExt pw)
  where
  Pf = fst FF
  Pg = fst GG
  pw : ∀ γ → P FF γ ≡ P GG γ
  pw = elimProp {P = λ γ → P FF γ ≡ P GG γ}
    (λ γ → isSetHProp (P FF γ) (P GG γ))
    refl
    (λ {z} _ → Σ≡Prop (λ _ → isPropIsProp) (hPropExt (snd (P FF (suc z))) (snd (P GG (suc z)))
      (λ H m → rec (str (fst (Pg m) (suc z))) (λ { (n , incl) → incl (suc z) (H n) }) (G≼F m))
      (λ H n → rec (str (fst (Pf n) (suc z))) (λ { (m , incl) → incl (suc z) (H m) }) (F≼G n))))
    (λ {w} _ → Σ≡Prop (λ _ → isPropIsProp) (hPropExt (snd (P FF (lim w))) (snd (P GG (lim w)))
      (λ H m → rec squash₁ (λ { (n , incl) → rec squash₁ (λ { (k , Hk) → ∣ k , incl (fst w k) Hk ∣₁ }) (H n) }) (G≼F m))
      (λ H n → rec squash₁ (λ { (m , incl) → rec squash₁ (λ { (k , Hk) → ∣ k , incl (fst w k) Hk ∣₁ }) (H m) }) (F≼G n))))

open Assigning ι succ sup-A supPath

-- monotonicity of `succ` in `≦`, by `elimProp` on γ (prop-valued).
s≦s : ∀ {x y} → x ≦ y → succ x ≦ succ y
s≦s {x} {y} h = elimProp {P = λ γ → typ (fst (succ y) γ) → typ (fst (succ x) γ)}
  (λ γ → isPropΠ λ _ → str (fst (succ x) γ))
  ⊥-rec
  (λ {z} _ → h z)
  (λ {f} ih → rec squash₁ (λ { (n , H) → ∣ n , ih n H ∣₁ }))

-- cocone: `xx ≦ (α'ₙ ≤ᵖ_)` lifts to `xx ≦ (lim α' ≤ᵖ_)`, via the inversion `inv`.
≦l : ∀ {n} F x → (x ≦ fst F n) → x ≦ sup-A F
≦l {n} F x h γ H = h γ (inv F γ H n)

-- supremum: if every `α'ₙ ≤ᵖ_` is `≦ xx`, then `lim α' ≤ᵖ_` is, via `bound`.
l≦ : ∀ F x → (∀ n → fst F n ≦ x) → sup-A F ≦ x
l≦ F x hs γ H = bound F γ (λ n → hs n γ H)

-- (`ι≦` inlined: zero's predicate `Unit` is above everything, trivially.)
open Satisfying isSetA isProp≦ (λ {_} _ _ → tt) s≦s ≦l l≦ ≦-trans
```

Finally the order-code: `α ≤ᵖ β` is the predicate `elim α` evaluated at `β`. It
is **non-recursive** — `fst ∘ elim` — so it passes the termination checker with
no pragma.

```agda
-- the reconstructed order: NON-RECURSIVE (delegates to the external `elim`).
_≤ᵖ_ : Ord → Ord → hProp ℓ-zero
α ≤ᵖ β = fst (elim α) β
```
