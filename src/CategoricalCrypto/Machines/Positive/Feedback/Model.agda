{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Machines.Positive.Feedback.Model where

open import Categories.Category.Monoidal.Bundle
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)
open import Data.Sum.Base
open import Level
open import CategoricalCrypto.Iface
import CategoricalCrypto.UC.Model.Seal as Seal
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Feedback as Raw
import CategoricalCrypto.Machines.Positive.Repack as Re

private
  module O = MonoidalCategory Seal.𝔾ᵒ
  module T = MonoidalCategory Model.𝔾₊
  module F = StrongMonoidalFunctor Model.forget-probabilities
  module FF = Functor F.F
  module R = Re.At 0ℓ
  variable A B C : Iface

feedbackₚ : Seal.ifaceᵒ (A ⊗ᴵ C) O.⇒ Seal.ifaceᵒ (B ⊗ᴵ C)
          → Seal.ifaceᵒ A O.⇒ Seal.ifaceᵒ B
feedbackₚ f = Seal.procᵒ (Raw.feedbackₚ (Seal.unprocᵒ f))

feedback : Seal.ifaceᵒ (A ⊗ᴵ C) T.⇒ Seal.ifaceᵒ (B ⊗ᴵ C)
         → Seal.ifaceᵒ A T.⇒ Seal.ifaceᵒ B
feedback = feedbackₚ

feedbackₚ-resp : {f g : Seal.ifaceᵒ (A ⊗ᴵ C) O.⇒ Seal.ifaceᵒ (B ⊗ᴵ C)}
                → f O.≈ g → feedbackₚ f O.≈ feedbackₚ g
feedbackₚ-resp eq = Seal.≈ᴹ⇒≈ᵒ (Raw.feedbackₚ-resp (Seal.≈ᵒ⇒≈ᴹ eq))

opaque
  unfolding Seal.𝔾ᵒ Seal.ifaceᵒ Seal.procᵒ Seal.unprocᵒ Model.positive-congruence Model._≈⁺_

  feedback-resp : {f g : Seal.ifaceᵒ (A ⊗ᴵ C) T.⇒ Seal.ifaceᵒ (B ⊗ᴵ C)}
                 → f T.≈ g → feedback f T.≈ feedback g
  feedback-resp {f = f} {g} eq = R.QS._○ᴹ_ (Raw.repack-feedback (Seal.unprocᵒ f))
    (R.QS._○ᴹ_ (Raw.feedback-resp eq) (R.QS.⟺ᴹ (Raw.repack-feedback (Seal.unprocᵒ g))))

  pack-feedback : (f : R.Q.Machine ((Pos A ⊎ Pos C) ⊎ (Neg B ⊎ Neg C))
                                   ((Neg A ⊎ Neg C) ⊎ (Pos B ⊎ Pos C)))
    → Model.pack-positive {A} {B} (Raw.feedback₊ f) T.≈
        feedback {A} {C} {B} (Model.pack-positive {A ⊗ᴵ C} {B ⊗ᴵ C} f)
  pack-feedback f = R.QS._○ᴹ_ (R.repack-unpack (Raw.feedback₊ f))
    (R.QS._○ᴹ_ (Raw.feedback-resp (R.QS.⟺ᴹ (R.repack-unpack f)))
      (R.QS.⟺ᴹ (Raw.repack-feedback (R.unpack f))))

preserves-feedback : (f : Seal.ifaceᵒ (A ⊗ᴵ C) O.⇒ Seal.ifaceᵒ (B ⊗ᴵ C))
  → FF.F₁ (feedbackₚ f) T.≈ feedback (FF.F₁ f)
preserves-feedback f = T.Equiv.refl
