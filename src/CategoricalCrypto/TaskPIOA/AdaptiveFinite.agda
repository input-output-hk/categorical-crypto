{-# OPTIONS --safe --without-K #-}

-- Unlike runFrom, a padded word retains the reply of every activation,
-- including hidden and disabled activations.
module CategoricalCrypto.TaskPIOA.AdaptiveFinite where

open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe)
open import Data.Product.Base

open import CategoricalCrypto.TaskPIOA.Core
open import ProbabilisticLogic.Distribution.RationalDist

paddedReplyRun : ∀ {S} (M : Automaton S) → Schedule S → State M
  → Dist-ℚ (List (Maybe (Output S)))
paddedReplyRun M [] q = return-ℚ []
paddedReplyRun M (t ∷ ρ) q = tick M t q >>=ᴹ λ (o , q′) →
  Dmap (o ∷_) (paddedReplyRun M ρ q′)
