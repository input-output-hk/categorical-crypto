{-# OPTIONS --safe #-}

module CategoricalCrypto.Machine.Relational.Isomorphism where

open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
import CategoricalCrypto.Machine.Iso as Iso
open import CategoricalCrypto.Machine.Relational

private variable A B : Channel

-- The state bijection alone says nothing about the chosen initial predicates.
lift-iso : {P Q : Initialized A B} (φ : machine P Iso.≅ᴹ machine Q)
  → (∀ {s} → initial P s → initial Q (Iso._≅ᴹ_.to φ s))
  → (∀ {t} → initial Q t → initial P (Iso._≅ᴹ_.from φ t))
  → P ≈ᴿ Q
lift-iso {P = P} {Q} φ forward backward = record
  { Related = λ s t → to s ≡ t
  ; initial-to = λ p → _ , forward p , refl
  ; initial-from = λ { {t} q → _ , backward q , to∘from t }
  ; step-to = λ { refl p → _ , iso-step-to p , refl }
  ; step-from = λ { {s} refl q → _ ,
      subst (λ z → M.Machine.stepRel (machine P) z _ _ _) (from∘to s) (iso-step-from q) , to∘from _ }
  }
  where open Iso._≅ᴹ_ φ renaming (step-to to iso-step-to; step-from to iso-step-from)

all-states : M.Machine A B → Initialized A B
all-states m = initialize m λ _ → ⊤

all-states-cong : {m n : M.Machine A B} → m Iso.≅ᴹ n → all-states m ≈ᴿ all-states n
all-states-cong φ = lift-iso φ (λ _ → tt) (λ _ → tt)

-- Useful for closed structural diagrams: their product predicates are inhabited
-- at every state, although they are not definitionally the constant predicate.
total-iso : {P Q : Initialized A B} → machine P Iso.≅ᴹ machine Q
  → (∀ s → initial P s) → (∀ t → initial Q t) → P ≈ᴿ Q
total-iso φ p q = lift-iso φ (λ _ → q _) (λ _ → p _)
