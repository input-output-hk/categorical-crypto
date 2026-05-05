{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; _⊗_; isEquivalence; trans)

open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

import Data.List.NonEmpty as NE
open import Data.Nat using (_≤_)
open import Data.Rational as ℚ using (ℚ; _/_)
open import Data.Integer using (+_)

open import ProbabilisticLogic.Abstract
open import ProbabilisticLogic.Reasoning

module ProbabilisticLogic.Distribution.Binomial c ℓ (a : Abstract c ℓ) where

open Abstract a
open import ProbabilisticLogic.Distribution.Bernoulli c ℓ a

private module Eq = Setoid setoid

------------------------------------------------------------------------
-- The Binomial distribution as a product of Bernoullis.

-- The k-fold trial space: a nested product of `Bool`.
Bool^ : ℕ → Type
Bool^ zero    = ⊤
Bool^ (suc k) = Bool × Bool^ k

-- The Binomial distribution: k independent Bernoulli(m / (m + n)) trials,
-- assembled as the product distribution `bernoulli ⊗ bernoulli ⊗ ⋯ ⊗ bernoulli`.
-- A point of the sample space records the outcome of every trial.
binomial : (k m n : ℕ) ⦃ _ : NonZero (m +ℕ n) ⦄ → ProbDistr (Bool^ k)
binomial zero    m n = empirical (tt NE.∷ [])
binomial (suc k) m n = bernoulli m n ⊗ binomial k m n

------------------------------------------------------------------------
-- Predicates on outcomes.

-- Number of trials that landed `true`.
count : ∀ {k} → Bool^ k → ℕ
count {zero}  _              = 0
count {suc k} (false , bs)   = count bs
count {suc k} (true  , bs)   = suc (count bs)

-- Exactly i trials are true.
exactly : ∀ {k} → ℕ → Bool^ k → Type
exactly i bs = count bs ≡ i

-- At least i trials are true.
at-least : ∀ {k} → ℕ → Bool^ k → Type
at-least i bs = i ≤ count bs

-- At most i trials are true.
at-most : ∀ {k} → ℕ → Bool^ k → Type
at-most i bs = count bs ≤ i

-- Every trial landed `true`.  Coincides with `exactly k` and `at-least k`
-- on a `Bool^ k` outcome.
all-true : ∀ {k} → Bool^ k → Type
all-true {zero}  _        = ⊤
all-true {suc k} (b , bs) = (↑ id) b × all-true bs

-- Every trial landed `false`.  Coincides with `exactly 0` and `at-most 0`.
all-false : ∀ {k} → Bool^ k → Type
all-false {zero}  _        = ⊤
all-false {suc k} (b , bs) = (↑ not) b × all-false bs

------------------------------------------------------------------------
-- Iterated multiplication on `Probability` and on `ℚ`.

pow : Probability → ℕ → Probability
pow _ zero    = 1#
pow p (suc k) = p * pow p k

pow-ℚ : ℚ → ℕ → ℚ
pow-ℚ _ zero    = + 1 / 1
pow-ℚ p (suc k) = p ℚ.* pow-ℚ p k

private
  pow-cong : ∀ k {x y} → x ≈ y → pow x k ≈ pow y k
  pow-cong zero    _   = Eq.refl
  pow-cong (suc k) x≈y = *-cong x≈y (pow-cong k x≈y)

  -- The Probability-level k-fold product of `fromℚ p` is the image of
  -- the ℚ-level k-fold product, by induction using `fromℚ-1` and
  -- `fromℚ-homomorphism`.
  pow-fromℚ : ∀ p k → pow (fromℚ p) k ≈ fromℚ (pow-ℚ p k)
  pow-fromℚ p zero    = Eq.sym fromℚ-1
  pow-fromℚ p (suc k) = begin
    fromℚ p * pow (fromℚ p) k       ≈⟨ *-congˡ (pow-fromℚ p k) ⟩
    fromℚ p * fromℚ (pow-ℚ p k)     ≈⟨ fromℚ-homomorphism ⟩
    fromℚ (p ℚ.* pow-ℚ p k)         ∎
    where open ≈-Reasoning setoid

------------------------------------------------------------------------
-- Probability that all trials succeed / all fail, in `pow` form.

-- Probability that all k trials succeed equals the k-th power of the
-- single-trial success probability.  Pure consequence of `⊗-rect`.
P-all-true : ∀ k m n ⦃ _ : NonZero (m +ℕ n) ⦄
           → binomial k m n ∙ all-true ≈ pow (bernoulli m n ∙ (↑ id)) k
P-all-true zero    m n = PU≈1
P-all-true (suc k) m n = begin
  binomial (suc k) m n ∙ all-true
    ≈⟨ ⊗-rect ⟩
  bernoulli m n ∙ (↑ id) * binomial k m n ∙ all-true
    ≈⟨ *-congˡ (P-all-true k m n) ⟩
  bernoulli m n ∙ (↑ id) * pow (bernoulli m n ∙ (↑ id)) k ∎
  where open ≈-Reasoning setoid

-- Probability that all k trials fail equals the k-th power of the
-- single-trial failure probability.  Symmetric to `P-all-true`.
P-all-false : ∀ k m n ⦃ _ : NonZero (m +ℕ n) ⦄
            → binomial k m n ∙ all-false ≈ pow (bernoulli m n ∙ (↑ not)) k
P-all-false zero    m n = PU≈1
P-all-false (suc k) m n = begin
  binomial (suc k) m n ∙ all-false
    ≈⟨ ⊗-rect ⟩
  bernoulli m n ∙ (↑ not) * binomial k m n ∙ all-false
    ≈⟨ *-congˡ (P-all-false k m n) ⟩
  bernoulli m n ∙ (↑ not) * pow (bernoulli m n ∙ (↑ not)) k ∎
  where open ≈-Reasoning setoid

------------------------------------------------------------------------
-- Probabilities expressed directly as `fromℚ` of a rational power.

-- Probability that all k trials succeed = (m / (m + n))^k as a rational.
P-all-true-ℚ : ∀ k m n ⦃ _ : NonZero (m +ℕ n) ⦄
             → binomial k m n ∙ all-true ≈ fromℚ (pow-ℚ (+ m / (m +ℕ n)) k)
P-all-true-ℚ k m n = begin
  binomial k m n ∙ all-true                  ≈⟨ P-all-true k m n ⟩
  pow (bernoulli m n ∙ (↑ id)) k             ≈⟨ pow-cong k (P-bernoulli-true m n) ⟩
  pow (fromℚ (+ m / (m +ℕ n))) k             ≈⟨ pow-fromℚ (+ m / (m +ℕ n)) k ⟩
  fromℚ (pow-ℚ (+ m / (m +ℕ n)) k)           ∎
  where open ≈-Reasoning setoid

-- Probability that all k trials fail = (n / (m + n))^k as a rational.
P-all-false-ℚ : ∀ k m n ⦃ _ : NonZero (m +ℕ n) ⦄
              → binomial k m n ∙ all-false ≈ fromℚ (pow-ℚ (+ n / (m +ℕ n)) k)
P-all-false-ℚ k m n = begin
  binomial k m n ∙ all-false                 ≈⟨ P-all-false k m n ⟩
  pow (bernoulli m n ∙ (↑ not)) k            ≈⟨ pow-cong k (P-bernoulli-false m n) ⟩
  pow (fromℚ (+ n / (m +ℕ n))) k             ≈⟨ pow-fromℚ (+ n / (m +ℕ n)) k ⟩
  fromℚ (pow-ℚ (+ n / (m +ℕ n)) k)           ∎
  where open ≈-Reasoning setoid
