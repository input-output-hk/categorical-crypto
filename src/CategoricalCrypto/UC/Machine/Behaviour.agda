{-# OPTIONS --safe --without-K --guardedness #-}

-- Behavioural equality of machines (maurer2002 Defs 9–10): every `Strat`
-- distinguisher sees both verdict masses agree up to every positive slack.
-- `_≈ₚ_` would be too fine: a rejection-sampled bit and `coinₚ` are one random
-- system but two `_≈ₚ_`-classes.  See docs/uc-setup-random-systems.md §3.1–3.2.

open import Level
open import Relation.Binary.Structures

open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Run

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Behaviour where

private
  module Ap = AllPositive ℚ-refinement Approximationᴹ
  module MC = Core (𝒱ₚ 0ℓ)
  module MS = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  variable X Y : Set

infix 4 _≈ᴿ_

_≈ᴿ_ : MC.Machine X Y → MC.Machine X Y → Set
_≈ᴿ_ {X} {Y} f g = (d : Strat X Y) → runˢ f d Ap.∼ᵃ runˢ g d

≈ᴿ-isEquivalence : {X Y : Set} → IsEquivalence (_≈ᴿ_ {X} {Y})
≈ᴿ-isEquivalence = record
  { refl  = λ _ → refl
  ; sym   = λ e d → sym (e d)
  ; trans = λ e e′ d → trans (e d) (e′ d)
  }
  where open IsEquivalence Ap.∼ᵃ-isEquivalence

≈ᴹ⇒≈ᴿ : {f g : MC.Machine X Y} → f MS.≈ᴹ g → f ≈ᴿ g
≈ᴹ⇒≈ᴿ e d = Ap.zero⇒positive (≈ₚ⇒≈ₚ[0] (runˢ-resp-≈ᴹ e d))
