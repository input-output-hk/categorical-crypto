{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Structural identities at the FinBij level.
--
-- These are the bijection-level coherence lemmas required by the
-- canonical-form / faithfulness work for list permutations.
------------------------------------------------------------------------

module Categories.PermuteCoherence.Coxeter.EvalSoundness where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (suc)
open import Data.Fin.Patterns using (0F)

import Data.Fin.Permutation as P

open import Relation.Binary.PropositionalEquality.Core using (refl; sym)

open import Categories.PermuteCoherence.FinBij

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Structural coherence of `cons-fb` and `swap-fb` at the FinBij level.

cons-fb-functor-id : cons-fb (id-fb {n = n}) ≈-fb id-fb {n = suc n}
cons-fb-functor-id = P.lift₀-id

-- `cons-fb` twice on the identity: needed by `WordInterp.gen-eval`'s base
-- case and by six sites of `FaithfulnessInductive.sound`.  By cases, not by
-- chaining `cons-fb-functor-id` — chaining wants `Word.cons-fb-cong`, and
-- `Word` imports THIS module.
cons²-fb-id : cons-fb (cons-fb (id-fb {n = n})) ≈-fb id-fb {n = suc (suc n)}
cons²-fb-id 0F            = refl
cons²-fb-id (suc 0F)      = refl
cons²-fb-id (suc (suc i)) = refl

cons-fb-functor-comp : ∀ {n m k} (g : FinBij m k) (f : FinBij n m) →
                       cons-fb (g ∘-fb f) ≈-fb cons-fb g ∘-fb cons-fb f
cons-fb-functor-comp g f i = sym (P.lift₀-comp f g i)

swap-fb-involutive : swap-fb n ∘-fb swap-fb n ≈-fb id-fb
swap-fb-involutive 0F            = refl
swap-fb-involutive (suc 0F)      = refl
swap-fb-involutive (suc (suc i)) = refl

swap-fb-natural : ∀ {n m} (f : FinBij n m) →
                  swap-fb m ∘-fb cons-fb (cons-fb f)
                  ≈-fb
                  cons-fb (cons-fb f) ∘-fb swap-fb n
swap-fb-natural f 0F             = refl
swap-fb-natural f (suc 0F)       = refl
swap-fb-natural f (suc (suc i))  = refl

-- Yang-Baxter (braid) relation.
yang-baxter : ∀ {n} →
  swap-fb (suc n) ∘-fb cons-fb (swap-fb n) ∘-fb swap-fb (suc n)
  ≈-fb
  cons-fb (swap-fb n) ∘-fb swap-fb (suc n) ∘-fb cons-fb (swap-fb n)
yang-baxter 0F                   = refl
yang-baxter (suc 0F)             = refl
yang-baxter (suc (suc 0F))       = refl
yang-baxter (suc (suc (suc i)))  = refl

