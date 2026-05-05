{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; _⊗_; isEquivalence; trans)

open import Algebra

open import Data.Rational as ℚ using (ℚ; _/_)
open import Data.Integer using (+_)

open import ProbabilisticLogic.Abstract
open import ProbabilisticLogic.Reasoning

module ProbabilisticLogic.Examples.MultipleCoins c ℓ (a : Abstract c ℓ) where

open Abstract a
open import ProbabilisticLogic.Logic c ℓ a
open import ProbabilisticLogic.Distribution.Bernoulli c ℓ a
open import ProbabilisticLogic.Distribution.Binomial c ℓ a

------------------------------------------------------------------------
-- Two independent fair coins both land `true` with probability ≥ 1/4.
-- The proof goes through the rational-form lemma `P-all-true-ℚ`, which
-- reduces the right-hand side to `fromℚ ((+ 1 / 2) ^ 2) = fromℚ (+ 1 / 4)`
-- definitionally.

two-fair-all : Σ[ binomial 2 1 1 ][ fromℚ (+ 1 / 4) ] all-true
two-fair-all .p≤PX = begin
  fromℚ (+ 1 / 4)              ≈⟨ P-all-true-ℚ 2 1 1 ⟨
  binomial 2 1 1 ∙ all-true    ∎
  where open ≤-Reasoning Probability

-- Two fair coins both `false` with probability ≥ 1/4 (symmetric).
two-fair-none : Σ[ binomial 2 1 1 ][ fromℚ (+ 1 / 4) ] all-false
two-fair-none .p≤PX = begin
  fromℚ (+ 1 / 4)              ≈⟨ P-all-false-ℚ 2 1 1 ⟨
  binomial 2 1 1 ∙ all-false   ∎
  where open ≤-Reasoning Probability

------------------------------------------------------------------------
-- Three independent biased coins (each `true` with prob 2/3) all land
-- `true` with probability ≥ 8/27, and all `false` with probability ≥ 1/27.

three-biased-all : Σ[ binomial 3 2 1 ][ fromℚ (+ 8 / 27) ] all-true
three-biased-all .p≤PX = begin
  fromℚ (+ 8 / 27)             ≈⟨ P-all-true-ℚ 3 2 1 ⟨
  binomial 3 2 1 ∙ all-true    ∎
  where open ≤-Reasoning Probability

three-biased-none : Σ[ binomial 3 2 1 ][ fromℚ (+ 1 / 27) ] all-false
three-biased-none .p≤PX = begin
  fromℚ (+ 1 / 27)             ≈⟨ P-all-false-ℚ 3 2 1 ⟨
  binomial 3 2 1 ∙ all-false   ∎
  where open ≤-Reasoning Probability
