{-# OPTIONS --safe --without-K #-}

-- Adaptive query strategies (distinguishers): decision trees over a query
-- interface, with a rational coin so randomized environments are first-class:
-- a deterministic strategy class is provably too weak for reflecting
-- environments (a fair coin choosing between two queries beats any single
-- deterministic tree).
--
-- `asks≤ n` bounds the ask-depth of every branch; coins are free.

open import Data.Bool.Base
open import Data.Empty
open import Data.Nat.Base as ℕ
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import ProbabilisticLogic.Distribution.RationalDist

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

-- A watch plays its argument unchanged and replaces the verdict by the
-- accumulated report of the (query, answer) pairs seen along the way.
watchFrom : (Q → R → Bool) → Bool → Strat Q R → Strat Q R
watchFrom report acc (out _)    = out acc
watchFrom report acc (ask q k)  = ask q λ r → watchFrom report (acc ∨ report q r) (k r)
watchFrom report acc (coin μ k) = coin μ λ b → watchFrom report acc (k b)

-- A watch buys no queries: it plays inside the allowance it is handed.
asks≤-watch : (report : Q → R → Bool) {n : ℕ} (acc : Bool) (d : Strat Q R)
            → asks≤ n d → asks≤ n (watchFrom report acc d)
asks≤-watch report acc (out b) _ = tt
asks≤-watch report {suc n} acc (ask q k) a = λ r → asks≤-watch report _ (k r) (a r)
asks≤-watch report acc (coin μ k) a = λ b → asks≤-watch report acc (k b) (a b)
