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
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

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

-- A watch plays its argument unchanged and replaces the verdict by the
-- accumulated report of the (query, answer) pairs seen along the way.  This is
-- the transformer `Examples.ChimericLedger.Observable.auditWatchFrom` is an
-- instance of, and `UC.Machine.Monitor.Agree` the monitor compiler implements.
watchFrom : (Q → R → Bool) → Bool → Strat Q R → Strat Q R
watchFrom report acc (out _)    = out acc
watchFrom report acc (ask q k)  = ask q λ r → watchFrom report (acc ∨ report q r) (k r)
watchFrom report acc (coin μ k) = coin μ λ b → watchFrom report acc (k b)

-- What ties a transformer to a report.  Three equations rather than
-- `watchFrom` itself: a transformer defined elsewhere satisfies them by
-- `refl`, where identifying the two definitions would want funext.
IsWatch : (Q → R → Bool) → (Bool → Strat Q R → Strat Q R) → Set
IsWatch {Q} {R} report w =
    ((acc b : Bool) → w acc (out b) ≡ out acc)
  × ( ((acc : Bool) (q : Q) (k : R → Strat Q R)
       → w acc (ask q k) ≡ ask q λ r → w (acc ∨ report q r) (k r))
    × ((acc : Bool) (μ : Dist-ℚ Bool) (k : Bool → Strat Q R)
       → w acc (coin μ k) ≡ coin μ λ b → w acc (k b)))

watchFrom-IsWatch : (report : Q → R → Bool) → IsWatch report (watchFrom report)
watchFrom-IsWatch _ = (λ _ _ → refl) , (λ _ _ _ → refl) , (λ _ _ _ → refl)

-- A watch buys no queries: it plays inside the allowance it is handed.
asks≤-watch : (report : Q → R → Bool) (w : Bool → Strat Q R → Strat Q R)
            → IsWatch report w → {n : ℕ} (acc : Bool) (d : Strat Q R)
            → asks≤ n d → asks≤ n (w acc d)
asks≤-watch report w iw@(eo , _ , _) {n} acc (out b) _ =
  subst (asks≤ n) (sym (eo acc b)) tt
asks≤-watch report w iw@(_ , ea , _) {suc n} acc (ask q k) a =
  subst (asks≤ (suc n)) (sym (ea acc q k)) λ r → asks≤-watch report w iw _ (k r) (a r)
asks≤-watch report w iw@(_ , _ , ec) {n} acc (coin μ k) a =
  subst (asks≤ n) (sym (ec acc μ k)) λ b → asks≤-watch report w iw acc (k b) (a b)
