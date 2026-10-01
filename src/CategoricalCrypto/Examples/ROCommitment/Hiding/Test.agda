{-# OPTIONS --safe --without-K #-}

-- Acceptance instances for the hiding bounds (`GamePlaying.Test`'s sense):
-- adaptive attacks that reach the places the games differ — `attackʰ` queries
-- a guessed opening point while the commitment is outstanding, `preqʰ` queries
-- the committer's point before it commits.  Read at `Hiding.Asymptotic`'s
-- entry points at digest length 5, where every bound bites (at 3, `εᵗ 3 3` is
-- 9/8).

open import Class.DecEq

open import Data.Bool.Base
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _/_)
  renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Unit.Base
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core

open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform

module CategoricalCrypto.Examples.ROCommitment.Hiding.Test where

open import CategoricalCrypto.Examples.ROCommitment.Extraction 5
open import CategoricalCrypto.Examples.ROCommitment.Hiding.Asymptotic
open import CategoricalCrypto.Examples.ROCommitment.Hiding.Game 5

import CategoricalCrypto.Examples.ROCommitment.Hiding.Game as G

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
        → ∣ Pr₁ (runWith (G.respIʰ 5) (G.sI₀ 5) (attackʰ d₀ r))
            -ℚ Pr₁ (runWith (G.respLʰ 5) (G.sL₀ 5) (attackʰ d₀ r)) ∣ℚ ≤ℚ εʰ 5 3
bounded d₀ r = hiding-boundⁿ 5 3 (attackʰ d₀ r) (attack-asks d₀ r)

preqʰ : Dig → Dig → Strat Qʰ Rʰ
preqʰ d₀ r = ask (askQʰ (true ∷ᵛ r)) λ v →
             ask (comQʰ true) λ a → out (echoed (published d₀ a) v)

preq-asks : (d₀ r : Dig) → asks≤ 2 (preqʰ d₀ r)
preq-asks d₀ r _ _ = tt

bounded-preq : (d₀ r : Dig)
             → ∣ Pr₁ (runWith (G.respIʰ 5) (G.sI₀ 5) (preqʰ d₀ r))
                 -ℚ Pr₁ (runWith (G.respRʰ 5) (G.sR₀ 5) (preqʰ d₀ r)) ∣ℚ
               ≤ℚ εᵗ 5 2
bounded-preq d₀ r = hiding-boundᵗ 5 2 (preqʰ d₀ r) (preq-asks d₀ r)

bounded-total : (d₀ r : Dig)
              → ∣ Pr₁ (runWith (G.respIʰ 5) (G.sI₀ 5) (attackʰ d₀ r))
                  -ℚ Pr₁ (runWith (G.respRʰ 5) (G.sR₀ 5) (attackʰ d₀ r)) ∣ℚ
                ≤ℚ εᵗ 5 3
bounded-total d₀ r = hiding-boundᵗ 5 3 (attackʰ d₀ r) (attack-asks d₀ r)

bites : εʰ 5 3 ≡ + 3 / 32
bites = refl

bites-total : εᵗ 5 3 ≡ + 9 / 32
bites-total = refl
