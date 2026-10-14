{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.MonoidalTests (Sort : Set) (Payload : Sort → Set) where

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Bundle
open import Categories.Functor.Presheaf
open import Level using (0ℓ; suc)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Category Sort Payload
open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Monoidal Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Plugging Sort Payload
import CategoricalCrypto.Standard2 as Standard
open import CategoricalCrypto.UCSetup using (UCSetup)

module M = MonoidalCategory OpenCSPᴹ

underlying-category : M.U ≡ OpenCSP
underlying-category = refl

tensor-object : ∀ A B → M._⊗₀_ A B ≡ (A ⊗₀ B)
tensor-object A B = refl

tensor-arrow : ∀ {A B C D} (f : Network A B) (g : Network C D) →
  M._⊗₁_ f g ≡ (f ⊗₁ g)
tensor-arrow f g = refl

tensor-unit : M.unit ≡ I
tensor-unit = refl

structural-associator-no-boxes : ∀ A B C →
  Boxes.shape (Network.components (M.associator.from {A} {B} {C})) ≡ empty
structural-associator-no-boxes A B C = refl

structural-associator-inverse-no-boxes : ∀ A B C →
  Boxes.shape (Network.components (M.associator.to {A} {B} {C})) ≡ empty
structural-associator-inverse-no-boxes A B C = refl

structural-left-unitor-no-boxes : ∀ A →
  Boxes.shape (Network.components (M.unitorˡ.from {A})) ≡ empty
structural-left-unitor-no-boxes A = refl

structural-right-unitor-no-boxes : ∀ A →
  Boxes.shape (Network.components (M.unitorʳ.from {A})) ≡ empty
structural-right-unitor-no-boxes A = refl

structural-left-unitor-inverse-no-boxes : ∀ A →
  Boxes.shape (Network.components (M.unitorˡ.to {A})) ≡ empty
structural-left-unitor-inverse-no-boxes A = refl

structural-right-unitor-inverse-no-boxes : ∀ A →
  Boxes.shape (Network.components (M.unitorʳ.to {A})) ≡ empty
structural-right-unitor-inverse-no-boxes A = refl

module TestingCompatibility (tests : Presheaf OpenCSP (Setoids (suc 0ℓ) (suc 0ℓ))) where
  module UC = Standard.StdUC OpenCSPᴹ tests

  setup-category : UCSetup.𝒞 UC.StdSetup ≡ OpenCSP
  setup-category = refl

  setup-grades : UCSetup.ℐ UC.StdSetup ≡ OpenCSPᴹ
  setup-grades = refl

  grade-action-object : ∀ X B → UC.T₀ X B ≡ (X ⊗₀ B)
  grade-action-object X B = refl

  grade-action-arrow : ∀ X {A B} (f : Network A B) →
    UC.T₁ X f ≡ (id {X} ⊗₁ f)
  grade-action-arrow X f = refl
