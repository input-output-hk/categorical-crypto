{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation where

open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational

private variable A B : Channel

record Presentation (R : Initialized A B) : Set₁ where
  open M.Machine (machine R)
  open Channel (A M.⊗ᵀ B)
  field
    initialₚ : Dₚ State
    stepₚ : State → inType → Dₚ (State × outType)
    initial-sound : ∀ {s} → Positive initialₚ s → initial R s
    initial-complete : ∀ {s} → initial R s → Positive initialₚ s
    step-sound : ∀ {s i o s′} → Positive (stepₚ s i) (s′ , o) → stepRel s i (just o) s′
    step-complete : ∀ {s i o s′} → stepRel s i (just o) s′ → Positive (stepₚ s i) (s′ , o)
    no-refusal : ∀ {s i s′} → stepRel s i nothing s′ → ⊥

open Presentation public

shadow : {R : Initialized A B} → Presentation R → Initialized A B
shadow {R = R} P = initialize (M.MkMachine relation) (Positive (initialₚ P))
  where
  relation : M.MachineType _ _ (M.Machine.State (machine R))
  relation s i (just o) s′ = Positive (stepₚ P s i) (s′ , o)
  relation s i nothing s′ = ⊥

presentation-correct : {R : Initialized A B} (P : Presentation R) → shadow P ≈ᴿ R
presentation-correct P = record
  { Related = _≡_
  ; initial-to = λ p → _ , initial-sound P p , refl
  ; initial-from = λ p → _ , initial-complete P p , refl
  ; step-to = λ { {o = just o} refl p → _ , step-sound P p , refl
                ; {o = nothing} refl () }
  ; step-from = λ { {o = just o} refl p → _ , step-complete P p , refl
                  ; {o = nothing} refl p → ⊥-elim (no-refusal P p) }
  }
