{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; _⊗_; isEquivalence; trans)

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

import Data.List.NonEmpty as NE
open import Data.Rational as ℚ using (ℚ; _/_)
open import Data.Integer using (+_)

open import ProbabilisticLogic.Abstract
open import ProbabilisticLogic.Reasoning

module ProbabilisticLogic.Examples.Weather c ℓ (a : Abstract c ℓ) where

open Abstract a
open import ProbabilisticLogic.Distribution.Markov c ℓ a

------------------------------------------------------------------------
-- A two-state weather Markov chain.
--
-- Transition probabilities:
--   sunny → 2/3 sunny, 1/3 rainy
--   rainy → 2/3 rainy, 1/3 sunny

data Weather : Type where
  sunny rainy : Weather

weather : StochasticMatrix Weather
weather sunny = weighted-K ((2 , sunny) NE.∷ (1 , rainy) ∷ [])
weather rainy = weighted-K ((2 , rainy) NE.∷ (1 , sunny) ∷ [])

isSunny : Weather → Bool
isSunny sunny = true
isSunny rainy = false

------------------------------------------------------------------------
-- Probability of `sunny` after starting `sunny` after n steps

P-step1-sunny : stepⁿ 1 weather sunny ∙ (↑ isSunny) ≈ fromℚ (+ 2 / 3)
P-step1-sunny = empirical-eq

P-step2-sunny : stepⁿ 2 weather sunny ∙ (↑ isSunny) ≈ fromℚ (+ 5 / 9)
P-step2-sunny = empirical-eq

P-step3-sunny : stepⁿ 3 weather sunny ∙ (↑ isSunny) ≈ fromℚ (+ 14 / 27)
P-step3-sunny = empirical-eq
