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
open import Data.Nat.Base as ℕ
open import Data.Unit.Base

open import ProbabilisticLogic.Prelude

module CategoricalCrypto.Strategy where

private variable Q Q′ R R′ : Set

data Strat (Q R : Set) : Set where
  out  : Bool → Strat Q R
  ask  : Q → (R → Strat Q R) → Strat Q R
  coin : Dist-ℚ Bool → (Bool → Strat Q R) → Strat Q R

asks≤ : ℕ → Strat Q R → Set
asks≤ _       (out _)    = ⊤
asks≤ zero    (ask _ _)  = ⊥
asks≤ (suc n) (ask _ k)  = ∀ r → asks≤ n (k r)
asks≤ n       (coin _ k) = ∀ b → asks≤ n (k b)

asks≤-mono : {n m : ℕ} → n ℕ.≤ m → (d : Strat Q R) → asks≤ n d → asks≤ m d
asks≤-mono le         (out _)    h = tt
asks≤-mono (s≤s le)   (ask _ k)  h = λ r → asks≤-mono le (k r) (h r)
asks≤-mono le         (coin _ k) h = λ b → asks≤-mono le (k b) (h b)

-- The same strategy read over another alphabet: asks relabelled forwards,
-- answers backwards.  One ask stays one ask, so no budget moves.
mapStrat : (Q → Q′) → (R′ → R) → Strat Q R → Strat Q′ R′
mapStrat u v (out b)    = out b
mapStrat u v (ask q k)  = ask (u q) λ r → mapStrat u v (k (v r))
mapStrat u v (coin μ k) = coin μ λ b → mapStrat u v (k b)

asks≤-mapStrat : {n : ℕ} (u : Q → Q′) (v : R′ → R) (d : Strat Q R)
               → asks≤ n d → asks≤ n (mapStrat u v d)
asks≤-mapStrat           u v (out _)    h = tt
asks≤-mapStrat {n = suc n} u v (ask _ k) h = λ r → asks≤-mapStrat u v (k (v r)) (h (v r))
asks≤-mapStrat           u v (coin _ k) h = λ b → asks≤-mapStrat u v (k b) (h b)
