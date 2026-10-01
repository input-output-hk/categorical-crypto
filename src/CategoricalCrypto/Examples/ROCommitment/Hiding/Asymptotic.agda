{-# OPTIONS --safe --without-K #-}

-- The hiding bounds at the security parameter, and their negligibility at the
-- identity schedule.  The contextual relation this ε would sit in is not
-- proved: `docs/fcom-hiding.md`.

open import Data.Nat.Base
open import Data.Nat.Poly
open import Data.Nat.Properties using (≤-refl)
open import Data.Rational
  renaming (_+_ to _+ℚ_; _*_ to _*ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (*-distribʳ-+; ≤-reflexive; ≤-trans)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Approximate.Decay
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform

import CategoricalCrypto.Examples.ROCommitment.Hiding.Defer as D
import CategoricalCrypto.Examples.ROCommitment.Hiding.Game as G

module CategoricalCrypto.Examples.ROCommitment.Hiding.Asymptotic where

εʰ : ℕ → ℕ → ℚ
εʰ n q = fromℕ q *ℚ inv-pow-2 n

εʰ-negligible : NegligibleBound εʰ
εʰ-negligible = negligibleBound-inv-pow-2 {t = λ _ q → q}
  (λ _ Pq → Pq) (λ _ → ≤-refl)

hiding-boundⁿ : (n m : ℕ) (d : Strat (G.Qʰ n) (G.Rʰ n)) → asks≤ m d
  → ∣ Pr₁ (runWith (G.respIʰ n) (G.sI₀ n) d) -ℚ Pr₁ (runWith (G.respLʰ n) (G.sL₀ n) d) ∣ℚ
    ≤ℚ εʰ n m
hiding-boundⁿ n = G.hiding-bound n

------------------------------------------------------------------------
-- …against the real protocol

-- `m·2⁻ⁿ` for the programming hop plus `2m·2⁻ⁿ` for the deferral hop
-- (`Hiding.Defer.defer-hiding`).
εᵗ : ℕ → ℕ → ℚ
εᵗ n q = fromℕ (q + (q + q)) *ℚ inv-pow-2 n

εᵗ-negligible : NegligibleBound εᵗ
εᵗ-negligible = negligibleBound-inv-pow-2 {t = λ _ q → q + (q + q)}
  (λ _ Pq → poly-+ Pq (poly-+ Pq Pq)) (λ _ → ≤-refl)

hiding-boundᵗ : (n m : ℕ) (d : Strat (G.Qʰ n) (G.Rʰ n)) → asks≤ m d
  → ∣ Pr₁ (runWith (G.respIʰ n) (G.sI₀ n) d) -ℚ Pr₁ (runWith (G.respRʰ n) (G.sR₀ n) d) ∣ℚ
    ≤ℚ εᵗ n m
hiding-boundᵗ n m d le = ≤-trans (D.hiding-bound-total n m d le) (≤-reflexive (sym collect))
  where
  collect : εᵗ n m ≡ G.εᴸ n m +ℚ fromℕ (m + m) *ℚ inv-pow-2 n
  collect = trans (cong (_*ℚ inv-pow-2 n) (fromℕ-+ m (m + m)))
                  (*-distribʳ-+ (inv-pow-2 n) (fromℕ m) (fromℕ (m + m)))
