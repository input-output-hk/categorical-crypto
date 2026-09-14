{-# OPTIONS --safe --without-K #-}

-- Acceptance instances for the hiding bounds: LIVE adaptive attacks that do
-- the things the games differ on — `attackʰ` commits, then queries the oracle
-- at a guessed opening point BEFORE the opening and reports whether that
-- query came back with the published digest; `preqʰ` queries the point the
-- committer is about to hash and reports whether the digest it publishes is
-- the answer it already has.  What they say is that the bounds' quantifiers
-- are inhabited by attacks that reach the disagreements, and not only by
-- strategies that stop before the protocol does anything.

open import Class.DecEq

open import Data.Bool.Base using (Bool; false; true)
open import Data.Nat.Base using (_+_)
open import Data.Rational using (ℚ)
  renaming (_+_ to _+ℚ_; _*_ to _*ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Relation.Nullary.Decidable.Core using (⌊_⌋)

open import CategoricalCrypto.Interaction using (runWith)
open import CategoricalCrypto.Strategy using (Strat; ask; asks≤; out)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (Pr₁)
open import ProbabilisticLogic.Distribution.Uniform using (fromℕ; inv-pow-2)

module CategoricalCrypto.Examples.ROCommitment.Hiding.Test where

open import CategoricalCrypto.Examples.ROCommitment.Extraction 3 using (Dig)
open import CategoricalCrypto.Examples.ROCommitment.Hiding.Defer 3
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

-- The commitment-time divergence: the point is in the table BEFORE the
-- committer hashes it, so the real game publishes what the adversary has
-- already seen and the deferred game publishes a fresh digest.
preqʰ : Dig → Dig → Strat Qʰ Rʰ
preqʰ d₀ r = ask (askQʰ (true ∷ᵛ r)) λ v →
             ask (comQʰ true) λ a → out (echoed (published d₀ a) v)

preq-asks : (d₀ r : Dig) → asks≤ 2 (preqʰ d₀ r)
preq-asks d₀ r _ _ = tt

bounded-preq : (d₀ r : Dig)
             → ∣ Pr₁ (runWith respIʰ sI₀ (preqʰ d₀ r))
                 -ℚ Pr₁ (runWith respRʰ sR₀ (preqʰ d₀ r)) ∣ℚ
               ≤ℚ εᴸ 2 +ℚ fromℕ (2 + 2) *ℚ inv-pow-2 3
bounded-preq d₀ r = hiding-bound-total 2 (preqʰ d₀ r) (preq-asks d₀ r)

bounded-total : (d₀ r : Dig)
              → ∣ Pr₁ (runWith respIʰ sI₀ (attackʰ d₀ r))
                  -ℚ Pr₁ (runWith respRʰ sR₀ (attackʰ d₀ r)) ∣ℚ
                ≤ℚ εᴸ 3 +ℚ fromℕ (3 + 3) *ℚ inv-pow-2 3
bounded-total d₀ r = hiding-bound-total 3 (attackʰ d₀ r) (attack-asks d₀ r)
