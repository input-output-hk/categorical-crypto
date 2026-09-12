{-# OPTIONS --safe --without-K #-}

-- The extraction bound read at the security parameter: one merged ε, and its
-- negligibility.
--
-- `Game.ε k m` is `(m² + m)·2⁻ᵏ + m·2⁻ᵏ`; merged into one numerator it is
-- `(m² + 2m)·2⁻ᵏ`, which is `UC.Approximate.Decay`'s shape and hence a
-- `NegligibleBound` at the identity schedule — the digest length IS the
-- security parameter here, so nothing has to keep up with it.
--
-- This is one of the two explicit components the consolidation plan's §3.3
-- witness form asks for; the other is the simulator's query certificate
-- (`Examples.ROCommitment.UC.simQB`).  The contextual relation the two would
-- sit in front of is NOT proved: `docs/fcom-extraction.md` states the residual
-- and what it would cost.

open import Data.Nat.Base using (ℕ; _*_; _+_)
open import Data.Nat.Poly using (Poly; poly-*; poly-+)
open import Data.Nat.Properties using (≤-refl)
open import Data.Rational using (ℚ)
  renaming (_*_ to _*ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (*-distribʳ-+; ≤-reflexive; ≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)

open import CategoricalCrypto.Interaction using (runWith)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate using (NegligibleBound)
open import CategoricalCrypto.UC.Approximate.Decay using (negligibleBound-inv-pow-2)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (Pr₁)
open import ProbabilisticLogic.Distribution.Uniform using (fromℕ; fromℕ-+; inv-pow-2)

import CategoricalCrypto.Examples.ROCommitment.Game as G

module CategoricalCrypto.Examples.ROCommitment.Asymptotic where

εᶜ : ℕ → ℕ → ℚ
εᶜ n q = fromℕ (q * q + q + q) *ℚ inv-pow-2 n

εᶜ-negligible : NegligibleBound εᶜ
εᶜ-negligible = negligibleBound-inv-pow-2 {t = λ _ q → q * q + q + q} {sch = λ n → n}
  (λ q Pq → poly-+ (poly-+ (poly-* Pq Pq) Pq) Pq) (λ _ → ≤-refl)

private
  merge : (n q : ℕ) → G.ε n q ≡ εᶜ n q
  merge n q = sym (trans (cong (_*ℚ inv-pow-2 n) (fromℕ-+ (q * q + q) q))
                         (*-distribʳ-+ (inv-pow-2 n) (fromℕ (q * q + q)) (fromℕ q)))

extraction-boundⁿ : (n m : ℕ) (d : Strat (G.Q n) (G.R n)) → asks≤ m d
  → ∣ Pr₁ (runWith (G.respI n) (G.sI₀ n) d) -ℚ Pr₁ (runWith (G.respR n) (G.sR₀ n) d) ∣ℚ
    ≤ℚ εᶜ n m
extraction-boundⁿ n m d a =
  ≤-trans (G.extraction-bound n m d a) (≤-reflexive (merge n m))
