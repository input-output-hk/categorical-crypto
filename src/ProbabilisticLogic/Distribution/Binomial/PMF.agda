{-# OPTIONS --without-K #-}

-- The full binomial probability mass function (PMF):
-- P(exactly i successes in k trials) = (k C i) · m^i · n^(k − i) / (m + n)^k.
--
-- This module is intentionally *not* `--safe`: it postulates two
-- ℚ-arithmetic identities (Pascal's recursion lifted to rationals) which
-- would follow from `Data.Nat.Combinatorics.nCk+nC[k+1]≡[n+1]C[k+1]`.
--
-- The probabilistic decomposition (a Bernoulli step on the head bit splits
-- `exactly (suc j)` into a disjoint union of two rectangles) is fully
-- proved.

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; _⊗_; isEquivalence; trans)

open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Unary using (_⊆_; _≐_; _∪_; ∅; U)

import Data.Nat as ℕ
open import Data.Nat using (_∸_; _^_)
open import Data.Nat.Combinatorics.Base using (_C_)
open import Data.Nat.Properties using (m^n≢0; suc-injective)
open import Data.Rational as ℚ using (ℚ; _/_)
open import Data.Integer using (+_)

open import ProbabilisticLogic.Abstract
open import ProbabilisticLogic.Reasoning

module ProbabilisticLogic.Distribution.Binomial.PMF c ℓ (a : Abstract c ℓ) where

open Abstract a
open import ProbabilisticLogic.Distribution.Bernoulli c ℓ a
open import ProbabilisticLogic.Distribution.Binomial c ℓ a

private module Eq = Setoid setoid

------------------------------------------------------------------------
-- Closed-form PMF.

pmf-ℚ : (k i m n : ℕ) ⦃ _ : NonZero (m +ℕ n) ⦄ → ℚ
pmf-ℚ k i m n = + ((k C i) ℕ.* (m ^ i) ℕ.* (n ^ (k ∸ i))) / ((m +ℕ n) ^ k)
  where instance _ = m^n≢0 (m +ℕ n) k

postulate
  -- Pascal's recursion lifted to rationals.
  pmf-ℚ-rec-zero : ∀ k m n ⦃ _ : NonZero (m +ℕ n) ⦄
                 → (+ n / (m +ℕ n)) ℚ.* pmf-ℚ k 0 m n
                 ≡ pmf-ℚ (suc k) 0 m n
  pmf-ℚ-rec-suc  : ∀ k j m n ⦃ _ : NonZero (m +ℕ n) ⦄
                 → ((+ m / (m +ℕ n)) ℚ.* pmf-ℚ k j m n)
                 ℚ.+ ((+ n / (m +ℕ n)) ℚ.* pmf-ℚ k (suc j) m n)
                 ≡ pmf-ℚ (suc k) (suc j) m n

------------------------------------------------------------------------
-- Event decompositions.

private
  -- For k = 0 the sample space is a singleton, so `exactly 0 ≐ U` and
  -- `exactly (suc i) ≐ ∅`.
  exactly-0-zero-≐-U : (λ (_ : Bool^ 0) → 0 ≡ 0) ≐ U
  exactly-0-zero-≐-U = (λ _ → tt) , (λ _ → P.refl)

  exactly-0-suc-≐-∅ : ∀ {i} → (λ (_ : Bool^ 0) → 0 ≡ suc i) ≐ ∅
  exactly-0-suc-≐-∅ = (λ ()) , (λ ())

  -- For k = suc k', `exactly 0` decomposes as `(↑ not) ⊠ exactly 0` only:
  -- the head bit must be `false`.
  exactly-suc-zero-≐ : ∀ {k} → exactly {suc k} 0 ≐ ((↑ not) ⊠ exactly 0)
  exactly-suc-zero-≐ = forward , backward
    where
      forward : ∀ {k} → exactly {suc k} 0 ⊆ ((↑ not) ⊠ exactly 0)
      forward {x = false , _} eq = tt , eq
      forward {x = true  , _} ()
      backward : ∀ {k} → ((↑ not) ⊠ exactly 0) ⊆ exactly {suc k} 0
      backward {x = false , _} (_  , eq) = eq
      backward {x = true  , _} (() , _)

  -- For k = suc k' and i = suc j, `exactly (suc j)` decomposes as the
  -- disjoint union of two rectangles.
  exactly-suc-suc-≐ : ∀ {k j} → exactly {suc k} (suc j)
                              ≐ ((↑ id) ⊠ exactly j) ∪ ((↑ not) ⊠ exactly (suc j))
  exactly-suc-suc-≐ = forward , backward
    where
      forward : ∀ {k j} → exactly {suc k} (suc j)
                        ⊆ ((↑ id) ⊠ exactly j) ∪ ((↑ not) ⊠ exactly (suc j))
      forward {x = true  , _} eq = inj₁ (tt , suc-injective eq)
      forward {x = false , _} eq = inj₂ (tt , eq)
      backward : ∀ {k j} → ((↑ id) ⊠ exactly j) ∪ ((↑ not) ⊠ exactly (suc j))
                         ⊆ exactly {suc k} (suc j)
      backward {x = true  , _} (inj₁ (_  , eq)) = P.cong suc eq
      backward {x = true  , _} (inj₂ (() , _))
      backward {x = false , _} (inj₁ (() , _))
      backward {x = false , _} (inj₂ (_  , eq)) = eq

  exactly-suc-suc-disjoint : ∀ {k j}
    → disjoint {Ω = Bool × Bool^ k}
        ((↑ id) ⊠ exactly j)
        ((↑ not) ⊠ exactly (suc j))
  exactly-suc-suc-disjoint {ω = true  , _} _        (() , _)
  exactly-suc-suc-disjoint {ω = false , _} (() , _) _

------------------------------------------------------------------------
-- The main theorem: the binomial PMF.

P-exactly-ℚ : ∀ k i m n ⦃ _ : NonZero (m +ℕ n) ⦄
            → binomial k m n ∙ exactly i ≈ fromℚ (pmf-ℚ k i m n)
P-exactly-ℚ zero zero m n = begin
  binomial 0 m n ∙ exactly 0    ≈⟨ ∙-cong exactly-0-zero-≐-U ⟩
  binomial 0 m n ∙ U            ≈⟨ PU≈1 ⟩
  1#                            ≈⟨ fromℚ-1 ⟨
  fromℚ (+ 1 / 1)               ∎
  where open ≈-Reasoning setoid
P-exactly-ℚ zero (suc i) m n = begin
  binomial 0 m n ∙ exactly (suc i) ≈⟨ ∙-cong exactly-0-suc-≐-∅ ⟩
  binomial 0 m n ∙ ∅               ≈⟨ P∅≈0 ⟩
  0#                               ≈⟨ fromℚ-0 ⟨
  fromℚ (+ 0 / 1)                  ∎
  where open ≈-Reasoning setoid
P-exactly-ℚ (suc k) zero m n = begin
  binomial (suc k) m n ∙ exactly 0
    ≈⟨ ∙-cong exactly-suc-zero-≐ ⟩
  binomial (suc k) m n ∙ ((↑ not) ⊠ exactly 0)
    ≈⟨ ⊗-rect ⟩
  bernoulli m n ∙ (↑ not) * binomial k m n ∙ exactly 0
    ≈⟨ *-cong (P-bernoulli-false m n) (P-exactly-ℚ k 0 m n) ⟩
  fromℚ (+ n / (m +ℕ n)) * fromℚ (pmf-ℚ k 0 m n)
    ≈⟨ fromℚ-homomorphism ⟩
  fromℚ ((+ n / (m +ℕ n)) ℚ.* pmf-ℚ k 0 m n)
    ≡⟨ P.cong fromℚ (pmf-ℚ-rec-zero k m n) ⟩
  fromℚ (pmf-ℚ (suc k) 0 m n)
    ∎
  where open ≈-Reasoning setoid
P-exactly-ℚ (suc k) (suc j) m n = begin
  binomial (suc k) m n ∙ exactly (suc j)
    ≈⟨ ∙-cong exactly-suc-suc-≐ ⟩
  binomial (suc k) m n ∙ (((↑ id) ⊠ exactly j) ∪ ((↑ not) ⊠ exactly (suc j)))
    ≈⟨ P-distrib-disjoint (exactly-suc-suc-disjoint {k} {j}) ⟨
  binomial (suc k) m n ∙ ((↑ id) ⊠ exactly j)
  + binomial (suc k) m n ∙ ((↑ not) ⊠ exactly (suc j))
    ≈⟨ +-cong ⊗-rect ⊗-rect ⟩
  bernoulli m n ∙ (↑ id) * binomial k m n ∙ exactly j
  + bernoulli m n ∙ (↑ not) * binomial k m n ∙ exactly (suc j)
    ≈⟨ +-cong (*-cong (P-bernoulli-true m n) (P-exactly-ℚ k j m n))
              (*-cong (P-bernoulli-false m n) (P-exactly-ℚ k (suc j) m n)) ⟩
  fromℚ (+ m / (m +ℕ n)) * fromℚ (pmf-ℚ k j m n)
  + fromℚ (+ n / (m +ℕ n)) * fromℚ (pmf-ℚ k (suc j) m n)
    ≈⟨ +-cong fromℚ-homomorphism fromℚ-homomorphism ⟩
  fromℚ ((+ m / (m +ℕ n)) ℚ.* pmf-ℚ k j m n)
  + fromℚ ((+ n / (m +ℕ n)) ℚ.* pmf-ℚ k (suc j) m n)
    ≈⟨ Eq.sym (fromℚ-+-homo _ _) ⟩
  fromℚ (((+ m / (m +ℕ n)) ℚ.* pmf-ℚ k j m n)
       ℚ.+ ((+ n / (m +ℕ n)) ℚ.* pmf-ℚ k (suc j) m n))
    ≡⟨ P.cong fromℚ (pmf-ℚ-rec-suc k j m n) ⟩
  fromℚ (pmf-ℚ (suc k) (suc j) m n)
    ∎
  where open ≈-Reasoning setoid

------------------------------------------------------------------------
-- Sample applications.

-- Two fair coins, exactly one `true`:  C(2,1)·(1/2)·(1/2) = 1/2.
two-fair-one : binomial 2 1 1 ∙ exactly 1 ≈ fromℚ (+ 1 / 2)
two-fair-one = P-exactly-ℚ 2 1 1 1

-- Three fair coins, exactly two `true`:  C(3,2)·(1/2)²·(1/2) = 3/8.
three-fair-two : binomial 3 1 1 ∙ exactly 2 ≈ fromℚ (+ 3 / 8)
three-fair-two = P-exactly-ℚ 3 2 1 1
