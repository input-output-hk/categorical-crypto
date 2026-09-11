{-# OPTIONS --safe --without-K #-}

-- The birthday potential: the collision mass a run of `j` more fresh uniform
-- samples can still accumulate against a pool that starts at `t` and grows by
-- one per sample.
--
--     Γ t j = (t + (t+1) + … + (t+j-1)) / 2ⁿ
--
-- `Γ-step` is the supermartingale's exact accounting — one sample spends
-- `t/2ⁿ`, which is what `Uniform.Collision.E-countMatch` charges it — and
-- `birthday` is the closed bound the headline ε is stated at: from a pool of
-- one, `q` samples cost at most `(q² + q)·2⁻ⁿ`.

open import Data.Nat.Base as ℕ using (ℕ; zero; suc; z≤n)
import Data.Nat.Properties as ℕₚ
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
open import Data.Rational.Properties using
  ( *-distribʳ-+; *-monoʳ-≤-nonNeg; *-zeroˡ; +-comm; +-identityʳ; +-mono-≤
  ; ≤-refl; ≤-reflexive; ≤-trans )
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform using
  ( 0≤fromℕ; 0≤inv-pow-2; fromℕ; fromℕ-+; fromℕ-mono-≤; inv-pow-2 )

module ProbabilisticLogic.Distribution.Uniform.Birthday (n : ℕ) where

private
  ε : ℚ
  ε = inv-pow-2 n

  0≤scaled : ∀ m → 0ℚ ≤ fromℕ m * ε
  0≤scaled m = ≤-trans (≤-reflexive (sym (*-zeroˡ ε)))
                       (*-monoʳ-≤-nonNeg ε ⦃ nonNegative (0≤inv-pow-2 n) ⦄ (0≤fromℕ m))

-- `j` consecutive naturals starting at `t`: a triangle slice.
sumN : ℕ → ℕ → ℕ
sumN t zero    = 0
sumN t (suc j) = t ℕ.+ sumN (suc t) j

Γ : ℕ → ℕ → ℚ
Γ t j = fromℕ (sumN t j) * ε

0≤Γ : ∀ t j → 0ℚ ≤ Γ t j
0≤Γ t j = 0≤scaled (sumN t j)

-- One sample's exact charge: `t/2ⁿ`, the pool it can collide with.
Γ-step : ∀ t j → fromℕ t * ε + Γ (suc t) j ≡ Γ t (suc j)
Γ-step t j = trans (sym (*-distribʳ-+ ε (fromℕ t) (fromℕ (sumN (suc t) j))))
                   (cong (_* ε) (sym (fromℕ-+ t (sumN (suc t) j))))

-- Spending a budget unit on a pool that has already grown costs no more than
-- spending it now.
Γ-suc : ∀ t j → Γ (suc t) j ≤ Γ t (suc j)
Γ-suc t j = ≤-trans (≤-reflexive (sym (+-identityʳ (Γ (suc t) j))))
              (≤-trans (≤-reflexive (+-comm (Γ (suc t) j) 0ℚ))
                (≤-trans (+-mono-≤ (0≤scaled t) ≤-refl) (≤-reflexive (Γ-step t j))))

private
  sumN-mono : ∀ t j → sumN t j ℕ.≤ sumN (suc t) j
  sumN-mono t zero    = z≤n
  sumN-mono t (suc j) = ℕₚ.+-mono-≤ (ℕₚ.n≤1+n t) (sumN-mono (suc t) j)

-- A pool that starts larger can accumulate more.
Γ-monoˡ : ∀ t j → Γ t j ≤ Γ (suc t) j
Γ-monoˡ t j = *-monoʳ-≤-nonNeg ε ⦃ nonNegative (0≤inv-pow-2 n) ⦄
                (fromℕ-mono-≤ (sumN-mono t j))

-- A step of budget left over is a step of budget gained.
Γ-mono : ∀ t j → Γ t j ≤ Γ t (suc j)
Γ-mono t j = *-monoʳ-≤-nonNeg ε ⦃ nonNegative (0≤inv-pow-2 n) ⦄
               (fromℕ-mono-≤ (ℕₚ.≤-trans (sumN-mono t j) (ℕₚ.m≤n+m (sumN (suc t) j) t)))

private
  -- Every one of the `j` summands is below `t + j`.
  sumN-≤ : ∀ t j → sumN t j ℕ.≤ j ℕ.* (t ℕ.+ j)
  sumN-≤ t zero    = z≤n
  sumN-≤ t (suc j) =
    subst (λ z → sumN t (suc j) ℕ.≤ suc j ℕ.* z) (sym (ℕₚ.+-suc t j))
      (ℕₚ.≤-trans (ℕₚ.+-monoʳ-≤ t (sumN-≤ (suc t) j))
        (ℕₚ.+-monoˡ-≤ (j ℕ.* suc (t ℕ.+ j))
                      (ℕₚ.≤-trans (ℕₚ.m≤m+n t j) (ℕₚ.n≤1+n (t ℕ.+ j)))))

  square : ∀ q → q ℕ.* (1 ℕ.+ q) ≡ q ℕ.* q ℕ.+ q
  square q = trans (ℕₚ.*-suc q q) (ℕₚ.+-comm q (q ℕ.* q))

-- The headline shape: from a pool of one, `q` samples cost at most
-- `(q² + q)·2⁻ⁿ`.
birthday : ∀ q → Γ 1 q ≤ fromℕ (q ℕ.* q ℕ.+ q) * ε
birthday q = *-monoʳ-≤-nonNeg ε ⦃ nonNegative (0≤inv-pow-2 n) ⦄
               (fromℕ-mono-≤ (ℕₚ.≤-trans (sumN-≤ 1 q) (ℕₚ.≤-reflexive (square q))))
