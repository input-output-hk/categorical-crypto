{-# OPTIONS --safe --without-K --guardedness #-}

-- The distinguishing advantage (maurer2002 Def 10, maurer2011cc §4.5) as a
-- relation in a rational slack: `Δ[ d ]⟨ f , g ⟩≤ ε` says that `d` sees both
-- verdict masses of `f` and `g` within `ε + δ` for every δ > 0.  A mass is a
-- supremum never formed (`Dp.Advantage`), so there is no number Δ^d(f, g),
-- and the slack is closed (`Approx.Rational.Closure`): then `_≈ᴿ_` is at once
-- Δ ≤ 0 and Δ ≤ ε at every ε > 0, and a bound survives a `≈ᴿ`-change of
-- either machine, so Δ is a distance on 𝔾ᴿ's homs.  See
-- docs/uc-setup-random-systems.md §4.4.

open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties
open import Function.Bundles
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Rational
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Machine.Run

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.UC.RandomSystems.Advantage where

private
  module MC = Core (𝒱ₚ 0ℓ)
  variable
    X Y : Set
    f f′ g g′ h : MC.Machine X Y
    ε ε′ : ℚ

-- Verdict laws compared at a closed slack.
module Verdict = Closure Approximationᴹ

infix 4 Δ[_]⟨_,_⟩≤_ _≈ᴿ[_]_

Δ[_]⟨_,_⟩≤_ : Strat X Y → MC.Machine X Y → MC.Machine X Y → ℚ → Set
Δ[ d ]⟨ f , g ⟩≤ ε = runˢ f d Verdict.≈̄[ ε ] runˢ g d

-- maurer2011cc §4.5's Δ^𝒟 with 𝒟 every `Strat`.
_≈ᴿ[_]_ : MC.Machine X Y → ℚ → MC.Machine X Y → Set
_≈ᴿ[_]_ {X} {Y} f ε g = (d : Strat X Y) → Δ[ d ]⟨ f , g ⟩≤ ε

private module C = Approximation Verdict.closure

-- maurer2002 Lemma 5(i), at every distinguisher at once.
≈ᴿ[]-trans : f ≈ᴿ[ ε ] g → g ≈ᴿ[ ε′ ] h → f ≈ᴿ[ ε ℚ.+ ε′ ] h
≈ᴿ[]-trans e e′ d = C.≈[]-trans (e d) (e′ d)

≈ᴿ[]-mono : ε ℚ.≤ ε′ → f ≈ᴿ[ ε ] g → f ≈ᴿ[ ε′ ] g
≈ᴿ[]-mono le e d = C.≈[]-mono le (e d)

-- One distinguisher's advantage and every distinguisher's, as approximations
-- of machines, so that `Approx.Rational.hybrid` applies to both.
advantage : Strat X Y → Approximation (MC.Machine X Y) ℚ-ordered 0ℓ
advantage d = record
  { _≈[_]_    = λ f ε g → Δ[ d ]⟨ f , g ⟩≤ ε
  ; ≈[]-refl  = C.≈[]-refl
  ; ≈[]-sym   = C.≈[]-sym
  ; ≈[]-trans = C.≈[]-trans
  ; ≈[]-mono  = C.≈[]-mono
  }

approxᴿ : Approximation (MC.Machine X Y) ℚ-ordered 0ℓ
approxᴿ = record
  { _≈[_]_    = _≈ᴿ[_]_
  ; ≈[]-refl  = λ _ → C.≈[]-refl
  ; ≈[]-sym   = λ e d → C.≈[]-sym (e d)
  ; ≈[]-trans = ≈ᴿ[]-trans
  ; ≈[]-mono  = ≈ᴿ[]-mono
  }

------------------------------------------------------------------------
-- Behavioural equality is the limit at zero, from above and at zero itself

≈ᴿ⇔≈ᴿ[0] : (f ≈ᴿ g) ⇔ (f ≈ᴿ[ 0ℚ ] g)
≈ᴿ⇔≈ᴿ[0] = mk⇔ (λ e d → Equivalence.from Verdict.≈̄[0]⇔∼ᵃ (e d))
               (λ e d → Equivalence.to Verdict.≈̄[0]⇔∼ᵃ (e d))

≈ᴿ⇔≈ᴿ[+] : (f ≈ᴿ g) ⇔ ((ε : ℚ) → 0ℚ ℚ.< ε → f ≈ᴿ[ ε ] g)
≈ᴿ⇔≈ᴿ[+] = mk⇔ (λ e ε pos → ≈ᴿ[]-mono (<⇒≤ pos) (Equivalence.to ≈ᴿ⇔≈ᴿ[0] e))
  λ h → Equivalence.from ≈ᴿ⇔≈ᴿ[0] λ d → Verdict.≈̄-closed λ δ pos →
          C.≈[]-mono (≤-reflexive (sym (+-identityˡ δ))) (h δ pos d)

-- …so a bound is one between behaviours: Δ descends to 𝔾ᴿ.
≈ᴿ[]-resp : f′ ≈ᴿ f → g ≈ᴿ g′ → f ≈ᴿ[ ε ] g → f′ ≈ᴿ[ ε ] g′
≈ᴿ[]-resp l r e d = Verdict.≈̄-resp-∼ᵃ (l d) (r d) (e d)
