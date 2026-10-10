{-# OPTIONS --safe --without-K #-}

-- A fair coin is blind to flipping its branches: the `Dist-ℚ` face of
-- `ProbabilisticLogic.Dp.Coin.coin-flip`, and the one-time pad's perfect
-- secrecy on one bit.

module ProbabilisticLogic.Distribution.Uniform.Flip where

open import Data.Bool.Base
open import Data.Rational
open import Data.Rational.Properties
open import Function.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.Uniform

uniform-not : (Q : Bool → ℚ) → lookupᴰℚ (entries uniform-Bool) Q ≡ lookupᴰℚ (entries uniform-Bool) (Q ∘ not)
uniform-not Q = swap (½ * Q false) (½ * Q true)
  where
  swap : ∀ a b → a + (b + 0ℚ) ≡ b + (a + 0ℚ)
  swap a b = trans (cong (a +_) (+-identityʳ b)) (trans (+-comm a b) (cong (b +_) (sym (+-identityʳ a))))

uniform-flip : ∀ {a} {A : Set a} {f g : Bool → Dist-ℚ A} → ((x : Bool) → f x ≈Mℚ g (not x))
             → (uniform-Bool >>=ᴹ f) ≈Mℚ (uniform-Bool >>=ᴹ g)
uniform-flip {f = f} {g} h P =
  trans (lookupᴰℚ-bind (entries uniform-Bool) (entries ∘ f) P)
  (trans (lookupᴰℚ-cong-P (entries uniform-Bool) (λ x → h x P))
  (trans (sym (uniform-not (λ x → lookupᴰℚ (entries (g x)) P)))
         (sym (lookupᴰℚ-bind (entries uniform-Bool) (entries ∘ g) P))))
