{-# OPTIONS --safe --without-K --guardedness #-}

-- The grading dictionary: `UC.Machine`'s direct relays read as the monoidal
-- spellings of the same processes, so that each stated field of
-- `UC.Machine.Grading.GradingLawsᴹ` becomes a corollary of a law of `𝒢ₚᴹ 0ℓ`.
--
-- Every object implicit is passed explicitly, for the reason
-- `UC.Machine.Grading`'s header gives.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle
  using (MonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Monad.Discrete using (DiscreteMonad)
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Utilities as MU

open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp using (Dₚ; returnₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
  using (Dₚ-DiscreteMonad; 𝒱ₚ; 𝒢ₚ; 𝒢ₚᴹ; distₚ; 𝒫ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.UC.Machine.Dictionary where

private
  module 𝒱 = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

open Core (𝒱ₚ 0ℓ)
open MD.MonoidalDistributive (distₚ 0ℓ)
open CE 𝒱.U cocartesian
open DiscreteMonad (Dₚ-DiscreteMonad {0ℓ}) hiding (_≈ᴹ_)
open KD (Dₚ-DiscreteMonad {0ℓ}) using (pureᵏ)
open MCat (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
open MU.Shorthands 𝔾.monoidal
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
open Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)

open import Categories.Category.Monoidal.Reasoning 𝒱.monoidal

private
  variable P Q R : Set
  variable V W V′ W′ : 𝒱.Obj

  -- The base's coproduct reassociators are the reassociating functions.
  assocˡᵏ : 𝒱._≈_ (α+⇐ {P} {Q} {R}) (pureᵏ ⊎assocˡ)
  assocˡᵏ (inj₁ _)        = >>=-identityˡ-≈
  assocˡᵏ (inj₂ (inj₁ _)) = >>=-identityˡ-≈
  assocˡᵏ (inj₂ (inj₂ _)) = ≈ᴹ.refl

  assocʳᵏ : 𝒱._≈_ (α+⇒ {P} {Q} {R}) (pureᵏ ⊎assocʳ)
  assocʳᵏ (inj₁ (inj₁ _)) = ≈ᴹ.refl
  assocʳᵏ (inj₁ (inj₂ _)) = >>=-identityˡ-≈
  assocʳᵏ (inj₂ _)        = >>=-identityˡ-≈

  -- The base half of the embedding `⌜ u , v ⌝`: swapping after relabelling each
  -- summand is the copairing that routes each summand to the other side.
  swap-copair : (u : 𝒱._⇒_ V W) (v : 𝒱._⇒_ V′ W′)
              → 𝒱._≈_ (𝒱._∘_ +-swap (u +₁ v)) [ 𝒱._∘_ i₂ u , 𝒱._∘_ i₁ v ]
  swap-copair u v = +-unique₂
    (𝒱.assoc ○ (refl⟩∘⟨ +₁∘i₁) ○ 𝒱.sym-assoc ○ (+-swap-i₁ ⟩∘⟨refl) ○ ⟺ inject₁)
    (𝒱.assoc ○ (refl⟩∘⟨ +₁∘i₂) ○ 𝒱.sym-assoc ○ (+-swap-i₂ ⟩∘⟨refl) ○ ⟺ inject₂)

  -- …and the machine half: an embedding of two pure machines is pure.
  ⌜⌝-pureᴹ : (u : 𝒱._⇒_ V W) (v : 𝒱._⇒_ V′ W′)
           → (σᴹ ∘ᴹ (pureᴹ u ⊗ᵉ pureᴹ v)) ≲ pureᴹ (𝒱._∘_ +-swap (u +₁ v))
  ⌜⌝-pureᴹ u v = ≲-trans (∘ᴹ-resp-≲ ≲-refl (⊗ᵉ-pureᴹ u v)) (pureᴹ-∘ +-swap (u +₁ v))

  -- A wire's step is the copairing of its two relabellings, crossed.
  wireStep-copair : {A B : Iface} (up : Pos A → Pos B) (down : Neg B → Neg A)
                  → 𝒱._≈_ (wireStep {A} {B} up down)
                      (𝒱._⊗₁_ 𝒱.id [ 𝒱._∘_ i₂ (pureᵏ up) , 𝒱._∘_ i₁ (pureᵏ down) ])
  wireStep-copair _ _ (_ , inj₁ _) =
    ≈ᴹ.sym (≈ᴹ.trans >>=-identityˡ-≈
                     (≈ᴹ.trans (>>=-cong-x >>=-identityˡ-≈) >>=-identityˡ-≈))
  wireStep-copair _ _ (_ , inj₂ _) =
    ≈ᴹ.sym (≈ᴹ.trans >>=-identityˡ-≈
                     (≈ᴹ.trans (>>=-cong-x >>=-identityˡ-≈) >>=-identityˡ-≈))

------------------------------------------------------------------------
-- The ancilla reassociators are the 𝒢-associator

a⇒-α⇐ : {X Y A : Iface}
      → 𝒫._≈_ {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ A}
          (a⇒ᴵ {X} {Y} {A}) (α⇐ {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ})
a⇒-α⇐ {X} {Y} {A} =
    ≲⇒≈ᴹ (mk-cong (wireStep-copair ⊎assocˡ ⊎assocʳ ○ ⟺ (refl⟩⊗⟨ bridge)))
  ○ᴹ ≲⇒≈ᴹ˘ (⌜⌝-pureᴹ α+⇐ α+⇒)
  where
  bridge = swap-copair α+⇐ α+⇒
         ○ []-cong₂ (refl⟩∘⟨ assocˡᵏ) (refl⟩∘⟨ assocʳᵏ)

a⇐-α⇒ : {X Y A : Iface}
      → 𝒫._≈_ {(X ⊗ᴵ Y) ⊗ᴵ A} {X ⊗ᴵ (Y ⊗ᴵ A)}
          (a⇐ᴵ {X} {Y} {A}) (α⇒ {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ})
a⇐-α⇒ {X} {Y} {A} =
    ≲⇒≈ᴹ (mk-cong (wireStep-copair ⊎assocʳ ⊎assocˡ ○ ⟺ (refl⟩⊗⟨ bridge)))
  ○ᴹ ≲⇒≈ᴹ˘ (⌜⌝-pureᴹ α+⇒ α+⇐)
  where
  bridge = swap-copair α+⇒ α+⇐
         ○ []-cong₂ (refl⟩∘⟨ assocʳᵏ) (refl⟩∘⟨ assocˡᵏ)
