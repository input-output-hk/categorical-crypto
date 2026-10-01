{-# OPTIONS --safe --without-K #-}

-- The extraction bound at the security parameter: `Game.ε` merged into one
-- numerator, `(m² + 2m)·2⁻ᵏ`, and its negligibility at the identity schedule
-- (the digest length is the security parameter).  The contextual relation
-- this ε would sit in is not proved: `docs/fcom-extraction.md`.

open import Data.Nat.Base
open import Data.Nat.Poly
open import Data.Nat.Properties using (≤-refl)
open import Data.Rational using (ℚ)
  renaming (_*_ to _*ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (*-distribʳ-+; ≤-reflexive; ≤-trans)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Approximate.Decay
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform

import CategoricalCrypto.Examples.ROCommitment.Game as G

module CategoricalCrypto.Examples.ROCommitment.Asymptotic where

εᶜ : ℕ → ℕ → ℚ
εᶜ n q = fromℕ (q * q + q + q) *ℚ inv-pow-2 n

εᶜ-negligible : NegligibleBound εᶜ
εᶜ-negligible = negligibleBound-inv-pow-2 {t = λ _ q → q * q + q + q}
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
