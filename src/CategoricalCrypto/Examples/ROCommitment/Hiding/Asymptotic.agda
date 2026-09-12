{-# OPTIONS --safe --without-K #-}

-- The hiding bound read at the security parameter, and its negligibility.
--
-- `Game.εᴸ k m` is `m·2⁻ᵏ` on the nose, so the merge the extraction side needs
-- (`Examples.ROCommitment.Asymptotic.εᶜ`) has nothing to do here: one query,
-- one guess at a `k`-bit point, one factor of `2⁻ᵏ`.  The digest length IS the
-- security parameter, so the schedule is the identity.
--
-- This is one of the two explicit components the consolidation plan's §3.3
-- witness form asks for; the other is `Hiding.UC.simQBʰ`.  The contextual
-- relation the two would sit in front of is NOT proved — `docs/fcom-hiding.md`
-- states the residual and which of the `graded-bridge` pieces it waits on.

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (≤-refl)
open import Data.Rational using (ℚ)
  renaming (_*_ to _*ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)

open import CategoricalCrypto.Interaction using (runWith)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate using (NegligibleBound)
open import CategoricalCrypto.UC.Approximate.Decay using (negligibleBound-inv-pow-2)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (Pr₁)
open import ProbabilisticLogic.Distribution.Uniform using (fromℕ; inv-pow-2)

import CategoricalCrypto.Examples.ROCommitment.Hiding.Game as G

module CategoricalCrypto.Examples.ROCommitment.Hiding.Asymptotic where

εʰ : ℕ → ℕ → ℚ
εʰ n q = fromℕ q *ℚ inv-pow-2 n

εʰ-negligible : NegligibleBound εʰ
εʰ-negligible = negligibleBound-inv-pow-2 {t = λ _ q → q} {sch = λ n → n}
  (λ _ Pq → Pq) (λ _ → ≤-refl)

hiding-boundⁿ : (n m : ℕ) (d : Strat (G.Qʰ n) (G.Rʰ n)) → asks≤ m d
  → ∣ Pr₁ (runWith (G.respIʰ n) (G.sI₀ n) d) -ℚ Pr₁ (runWith (G.respLʰ n) (G.sL₀ n) d) ∣ℚ
    ≤ℚ εʰ n m
hiding-boundⁿ n = G.hiding-bound n
