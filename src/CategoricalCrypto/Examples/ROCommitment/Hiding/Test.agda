{-# OPTIONS --safe --without-K #-}

-- Acceptance instance for the hiding bound: a LIVE adaptive attack that does
-- the one thing the two games differ on — commit, then query the oracle at a
-- guessed opening point BEFORE the opening, and report whether that query came
-- back with the published digest.  What it says is that the bound's quantifier
-- is inhabited by an attack that reaches the disagreement, and not only by
-- strategies that stop before the protocol does anything.

open import Class.DecEq

open import Data.Bool.Base using (Bool; false; true)
open import Data.Rational using (ℚ) renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Relation.Nullary.Decidable.Core using (⌊_⌋)

open import CategoricalCrypto.Interaction using (runWith)
open import CategoricalCrypto.Strategy using (Strat; ask; asks≤; out)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (Pr₁)

module CategoricalCrypto.Examples.ROCommitment.Hiding.Test where

open import CategoricalCrypto.Examples.ROCommitment.Extraction 3 using (Dig)
open import CategoricalCrypto.Examples.ROCommitment.Hiding.Game 3

-- The digest the committer published, falling back on `d₀` at an off-protocol
-- reply, and whether the oracle answered a query with it.
published : Dig → Rʰ → Dig
published _  (comRʰ c) = c
published d₀ _         = d₀

echoed : Dig → Rʰ → Bool
echoed c (ansRʰ d) = ⌊ d ≟ c ⌋
echoed _ _         = false

attackʰ : Dig → Dig → Strat Qʰ Rʰ
attackʰ d₀ r = ask (comQʰ true) λ a →
               ask (askQʰ (true ∷ᵛ r)) λ v →
               ask opnQʰ λ _ → out (echoed (published d₀ a) v)

attack-asks : (d₀ r : Dig) → asks≤ 3 (attackʰ d₀ r)
attack-asks d₀ r _ _ _ = tt

bounded : (d₀ r : Dig)
        → ∣ Pr₁ (runWith respIʰ sI₀ (attackʰ d₀ r))
            -ℚ Pr₁ (runWith respLʰ sL₀ (attackʰ d₀ r)) ∣ℚ ≤ℚ εᴸ 3
bounded d₀ r = hiding-bound 3 (attackʰ d₀ r) (attack-asks d₀ r)
