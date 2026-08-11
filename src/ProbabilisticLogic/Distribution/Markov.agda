{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; _⊗_; isEquivalence; trans)

import Data.List.NonEmpty as NE

open import ProbabilisticLogic.Abstract
open import ProbabilisticLogic.Reasoning

module ProbabilisticLogic.Distribution.Markov c ℓ (a : Abstract c ℓ) where

open Abstract a

------------------------------------------------------------------------
-- Stochastic matrices and Markov kernels.

-- A stochastic matrix on `S`: each row is a non-empty list of next
-- states whose multiplicities give the (rational) weights — the concrete
-- finite presentation.
StochasticMatrix : Type → Type
StochasticMatrix S = S → NE.List⁺ S

StochasticKernel : Type → Type c
StochasticKernel S = S → ProbDistr S

fromMatrix : ∀ {S} → StochasticMatrix S → StochasticKernel S
fromMatrix M = empirical P.∘ M

------------------------------------------------------------------------
-- The n-step distribution for a stochastic matrix.

stepⁿ-list : ∀ {S} → ℕ → StochasticMatrix S → S → NE.List⁺ S
stepⁿ-list zero    M s = s NE.∷ []
stepⁿ-list (suc n) M s = NE.concatMap M (stepⁿ-list n M s)

stepⁿ : ∀ {S} → ℕ → StochasticMatrix S → S → ProbDistr S
stepⁿ n M s = empirical (stepⁿ-list n M s)
