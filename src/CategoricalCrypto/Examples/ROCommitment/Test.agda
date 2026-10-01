{-# OPTIONS --safe --without-K #-}

-- Acceptance instance for the extraction bound (`GamePlaying.Test`'s sense):
-- an adaptive attack that queries the oracle, commits to the answer and opens
-- at the same point, so the bound's quantifier is inhabited by a run that
-- reaches the opening.  Read at `Asymptotic.extraction-boundⁿ` at digest
-- length 5, where the bound bites: at 3 it is 15/8.

open import Data.Bool.Base
open import Data.Integer.Base using (+_)
open import Data.Rational renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Unit.Base
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist.Expectation

module CategoricalCrypto.Examples.ROCommitment.Test where

open import CategoricalCrypto.Examples.ROCommitment.Asymptotic
open import CategoricalCrypto.Examples.ROCommitment.Extraction 5
open import CategoricalCrypto.Examples.ROCommitment.Game 5

answered : Dig → R → Dig
answered _  (ansR c) = c
answered d₀ _        = d₀

accepted : R → Bool
accepted (outR b) = b
accepted _        = false

attack : Dig → Dig → Strat Q R
attack d₀ r = ask (askQ (true ∷ᵛ r)) λ a →
              ask (comQ (answered d₀ a)) λ _ →
              ask (opnQ true r) λ v → out (accepted v)

attack-asks : (d₀ r : Dig) → asks≤ 3 (attack d₀ r)
attack-asks d₀ r _ _ _ = tt

bounded : (d₀ r : Dig)
        → ∣ Pr₁ (runWith respI sI₀ (attack d₀ r))
            -ℚ Pr₁ (runWith respR sR₀ (attack d₀ r)) ∣ℚ ≤ℚ εᶜ 5 3
bounded d₀ r = extraction-boundⁿ 5 3 (attack d₀ r) (attack-asks d₀ r)

bites : εᶜ 5 3 ≡ + 15 / 32
bites = refl
