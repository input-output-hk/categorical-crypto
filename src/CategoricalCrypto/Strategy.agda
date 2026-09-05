{-# OPTIONS --safe --without-K #-}

-- Adaptive query strategies (distinguishers): decision trees over a query
-- interface, with a rational coin so randomized environments are first-class
-- from day one — a deterministic strategy class is provably too weak for
-- reflecting environments (a fair coin choosing between two queries beats any
-- single deterministic tree).
--
-- `asks≤ n` bounds the ask-depth of every branch; coins are free.

open import Data.Bool.Base
open import Data.Empty
open import Data.Nat.Base
open import Data.Unit.Base

open import ProbabilisticLogic.Prelude

module CategoricalCrypto.Strategy where

private variable Q R : Set

data Strat (Q R : Set) : Set where
  out  : Bool → Strat Q R
  ask  : Q → (R → Strat Q R) → Strat Q R
  coin : Dist-ℚ Bool → (Bool → Strat Q R) → Strat Q R

asks≤ : ℕ → Strat Q R → Set
asks≤ _       (out _)    = ⊤
asks≤ zero    (ask _ _)  = ⊥
asks≤ (suc n) (ask _ k)  = ∀ r → asks≤ n (k r)
asks≤ n       (coin _ k) = ∀ b → asks≤ n (k b)
