{-# OPTIONS --safe --without-K #-}

-- The birthday potential: the collision mass a run of `j` more fresh uniform
-- samples can still accumulate against a pool that starts at `t` and grows by
-- one per sample.
--
--     Γ t j = (t + (t+1) + … + (t+j-1)) / 2ⁿ

open import Data.Nat.Base as ℕ using (ℕ; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Properties.Ext
open import Data.Rational
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform

module ProbabilisticLogic.Distribution.Uniform.Birthday (n : ℕ) where

private
  ε : ℚ
  ε = inv-pow-2 n

Γ : ℕ → ℕ → ℚ
Γ t j = fromℕ (sumN t j) * ε

0≤Γ : ∀ t j → 0ℚ ≤ Γ t j
0≤Γ t j = 0≤* (0≤fromℕ (sumN t j)) (0≤inv-pow-2 n)

-- One sample's exact charge: `t/2ⁿ`, the pool it can collide with.
Γ-step : ∀ t j → fromℕ t * ε + Γ (suc t) j ≡ Γ t (suc j)
Γ-step t j = trans (sym (*-distribʳ-+ ε (fromℕ t) (fromℕ (sumN (suc t) j))))
                   (cong (_* ε) (sym (fromℕ-+ t (sumN (suc t) j))))

Γ-suc : ∀ t j → Γ (suc t) j ≤ Γ t (suc j)
Γ-suc t j = ≤-trans (p≤q+p (Γ (suc t) j) (0≤* (0≤fromℕ t) (0≤inv-pow-2 n)))
                    (≤-reflexive (Γ-step t j))

Γ-monoˡ : ∀ t j → Γ t j ≤ Γ (suc t) j
Γ-monoˡ t j = *-monoʳ-≤-nonNeg ε ⦃ nonNegative (0≤inv-pow-2 n) ⦄
                (fromℕ-mono-≤ (sumN-mono t j))

Γ-mono : ∀ t j → Γ t j ≤ Γ t (suc j)
Γ-mono t j = ≤-trans (Γ-monoˡ t j) (Γ-suc t j)

birthday-bound : ℕ → ℚ
birthday-bound q = fromℕ (q ℕ.* q ℕ.+ q) * inv-pow-2 n

birthday : ∀ q → Γ 1 q ≤ birthday-bound q
birthday q = *-monoʳ-≤-nonNeg ε ⦃ nonNegative (0≤inv-pow-2 n) ⦄ (fromℕ-mono-≤
  (ℕₚ.≤-trans (sumN-≤ 1 q) (ℕₚ.≤-reflexive (trans (ℕₚ.*-suc q q) (ℕₚ.+-comm q (q ℕ.* q))))))
