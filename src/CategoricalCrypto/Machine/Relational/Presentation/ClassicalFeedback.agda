{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.ClassicalFeedback where

open import Axiom.ExcludedMiddle
open import Categories.Category.Monoidal.Bundle
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Function.Base using (id)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive.Monad
open import ProbabilisticLogic.Dp.Reasoning

import CategoricalCrypto.Channel.Core as Ch
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation.Descent using (channel; canonical)
import CategoricalCrypto.Machine.Relational.Presentation.Classical as Classical
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalWiring as Wiring
import CategoricalCrypto.Machine.Relational.Presentation.Feedback as Presentation
import CategoricalCrypto.Machine.Relational.Presentation.Positive as EP
import CategoricalCrypto.Machine.Relational.Wiring as W
import CategoricalCrypto.Machines.Positive.Feedback as Raw
import CategoricalCrypto.Machines.Positive.Feedback.Model as Public
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Pointwise as Point
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.UC.Machine as UC
import CategoricalCrypto.UC.Model.Seal as Seal

private
  module R = Re.At 0ℓ
  module Q = MonoidalCategory Model.𝔾₊
  variable A B C : Iface

module WithLEM (lem : ExcludedMiddle 0ℓ) where
  module Compile = Classical.WithLEM lem
  module Coherence = Wiring.WithLEM lem

  opaque
    unfolding Ch._⊗₀_ Compile.compile-step canonical

    tensor-canonical : UC.Proc (A ⊗ᴵ C) (B ⊗ᴵ C)
      → Initialized (channel A Ch.⊗₀ channel C) (channel B Ch.⊗₀ channel C)
    tensor-canonical f = canonical f

  opaque
    unfolding Ch._⊗₀_ Ch.construct-⊗ Ch.destruct-⊗ Compile.compile-step
              Coherence.present EP.positive-step tensor-canonical canonical
              Seal.𝔾ᵒ Seal.ifaceᵒ Seal.procᵒ Seal.unprocᵒ Model.positive-congruence

    preserves-feedbackₚ : (f : UC.Proc (A ⊗ᴵ C) (B ⊗ᴵ C))
      → canonical (Raw.feedbackₚ f) ≈ᴿ W.trace (tensor-canonical f)
    preserves-feedbackₚ {A} {C} {B} f = ≈ᴿ-trans
      (Compile.congruence (R.QS._○ᴹ_ (Raw.repack-feedback f)
        (Raw.feedback-resp (R.QS.⟺ᴹ normalized))))
      (Coherence.feedback (R.repack f))
      where
      retag : R.Q.Machine ((Pos A ⊎ Pos C) ⊎ (Neg B ⊎ Neg C))
                          ((Neg A ⊎ Neg C) ⊎ (Pos B ⊎ Pos C))
      retag = Presentation.tensor-positive (Coherence.present (R.repack f))

      step : (p : R.P.St f × ((Pos A ⊎ Pos C) ⊎ (Neg B ⊎ Neg C)))
        → R.Q.step retag p ≈ₚ R.P.step f p
      step (s , inj₁ (inj₁ a)) = map-eq _ _ id
        (λ { (s , inj₁ (inj₁ _)) → refl ; (s , inj₁ (inj₂ _)) → refl
           ; (s , inj₂ (inj₁ _)) → refl ; (s , inj₂ (inj₂ _)) → refl }) ⟨≈⟩ >>=ₚ-identityʳ _
      step (s , inj₁ (inj₂ c)) = map-eq _ _ id
        (λ { (s , inj₁ (inj₁ _)) → refl ; (s , inj₁ (inj₂ _)) → refl
           ; (s , inj₂ (inj₁ _)) → refl ; (s , inj₂ (inj₂ _)) → refl }) ⟨≈⟩ >>=ₚ-identityʳ _
      step (s , inj₂ (inj₁ b)) = map-eq _ _ id
        (λ { (s , inj₁ (inj₁ _)) → refl ; (s , inj₁ (inj₂ _)) → refl
           ; (s , inj₂ (inj₁ _)) → refl ; (s , inj₂ (inj₂ _)) → refl }) ⟨≈⟩ >>=ₚ-identityʳ _
      step (s , inj₂ (inj₂ c)) = map-eq _ _ id
        (λ { (s , inj₁ (inj₁ _)) → refl ; (s , inj₁ (inj₂ _)) → refl
           ; (s , inj₂ (inj₁ _)) → refl ; (s , inj₂ (inj₂ _)) → refl }) ⟨≈⟩ >>=ₚ-identityʳ _

      normalized : retag R.QS.≈ᴹ R.repack f
      normalized = R.QS.≲⇒≈ᴹ (Point.simFn id
        (λ _ → ≈ₚ⇒≈₊ (>>=ₚ-identityʳ _))
        (λ p → ≈ₚ⇒≈₊ (>>=ₚ-identityʳ _ ⟨≈⟩ step p)))

    preserves-public-feedback : (f : Seal.ifaceᵒ (A ⊗ᴵ C) Q.⇒ Seal.ifaceᵒ (B ⊗ᴵ C))
      → canonical (Seal.unprocᵒ (Public.feedback f)) ≈ᴿ W.trace (tensor-canonical (Seal.unprocᵒ f))
    preserves-public-feedback f = preserves-feedbackₚ (Seal.unprocᵒ f)
