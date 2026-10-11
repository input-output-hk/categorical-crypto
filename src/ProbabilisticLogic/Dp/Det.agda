{-# OPTIONS --safe --without-K --guardedness #-}

-- `detₚ`, the deterministic step that may refuse, is the `Maybe` monad's
-- image: it carries `Maybe.map` and Kleisli composition to `Dₚ`'s.

open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Function.Base
open import Level

open import ProbabilisticLogic.Dp

module ProbabilisticLogic.Dp.Det where

private variable
  a : Level
  A B : Set a

detₚ-map : (f : A → B) (m : Maybe A) → mapₚ f (detₚ m) ≈ₚ detₚ (Maybe.map f m)
detₚ-map f (just x) = >>=ₚ-identityˡ x (returnₚ ∘′ f)
detₚ-map f nothing  = bot-bind-≈ₚ (returnₚ ∘′ f)

detₚ->>= : (m : Maybe A) (f : A → Maybe B) → (detₚ m >>=ₚ (detₚ ∘′ f)) ≈ₚ detₚ (m Maybe.>>= f)
detₚ->>= (just x) f = >>=ₚ-identityˡ x (detₚ ∘′ f)
detₚ->>= nothing  f = bot-bind-≈ₚ (detₚ ∘′ f)
