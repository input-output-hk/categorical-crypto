{-# OPTIONS --safe --guardedness #-}

-- The exact literal positive-path shadow of a specified Dp presentation.
-- This is representation data, not a claim that arbitrary endpoint membership
-- descends through probabilistic equivalence or the behavioral quotient.
module CategoricalCrypto.Machine.Relational.Presentation.Canonical where

open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive
open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation

Stepₚ : Channel → Channel → Set → Set
Stepₚ A B S = S → Channel.inType (A M.⊗ᵀ B) → Dₚ (S × Channel.outType (A M.⊗ᵀ B))

fromₚ : {A B : Channel} {S : Set} → Dₚ S → Stepₚ A B S → Initialized A B
fromₚ d k = initialize (M.MkMachine relation) (Positive d)
  where
  relation : M.MachineType _ _ _
  relation s i (just o) s′ = Positive (k s i) (s′ , o)
  relation s i nothing s′ = ⊥

presentₚ : {A B : Channel} {S : Set} (d : Dₚ S) (k : Stepₚ A B S) → Presentation (fromₚ d k)
presentₚ d k = record
  { initialₚ = d ; stepₚ = k
  ; initial-sound = λ p → p ; initial-complete = λ p → p
  ; step-sound = λ p → p ; step-complete = λ p → p
  ; no-refusal = λ ()
  }
