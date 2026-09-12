{-# OPTIONS --safe --without-K #-}

-- Acceptance instance for the extraction bound, in `GamePlaying.Test`'s sense:
-- a LIVE adaptive adversary — query the oracle, commit at the answer it got,
-- open at the same pair — carried through `extraction-bound` to a concrete
-- ceiling.  What it says is that the bound's quantifier is inhabited by an
-- attack that actually reaches the opening, and not only by strategies that
-- stop before the protocol does anything.

open import Data.Bool.Base using (Bool; false; true)
open import Data.Rational using (ℚ) renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)

open import CategoricalCrypto.Interaction using (runWith)
open import CategoricalCrypto.Strategy using (Strat; ask; asks≤; out)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (Pr₁)

module CategoricalCrypto.Examples.ROCommitment.Test where

open import CategoricalCrypto.Examples.ROCommitment.Extraction 3 using (Dig)
open import CategoricalCrypto.Examples.ROCommitment.Game 3

-- The digest the adversary commits to: the one it was answered with, falling
-- back on `d₀` at an off-protocol reply.
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
            -ℚ Pr₁ (runWith respR sR₀ (attack d₀ r)) ∣ℚ ≤ℚ ε 3
bounded d₀ r = extraction-bound 3 (attack d₀ r) (attack-asks d₀ r)
