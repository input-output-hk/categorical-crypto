{-# OPTIONS --safe --without-K #-}

-- Morphisms of UC setups.

module CategoricalCrypto.UCSetup.Morphism where

open import Function.Bundles
open import Level
open import Relation.Binary.Bundles

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Presheaf
open import Categories.Functor.Presheaf.Morphism
open import Categories.Monad.Graded
open import Categories.Monad.Graded.Morphism

open import CategoricalCrypto.UCSetup

private variable
  o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ o₂ ℓ₂ e₂ o₂′ ℓ₂′ e₂′ o₃ ℓ₃ e₃ o₃′ ℓ₃′ e₃′ cs ℓs : Level

module _ (𝕊 : UCSetup o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ cs ℓs)
         (𝕊′ : UCSetup o₂ ℓ₂ e₂ o₂′ ℓ₂′ e₂′ cs ℓs) where
  private
    module S = UCSetup 𝕊
    module S′ = UCSetup 𝕊′

  record UCSetupMorphism : Set (o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₁′ ⊔ ℓ₁′ ⊔ e₁′
                                ⊔ o₂ ⊔ ℓ₂ ⊔ e₂ ⊔ o₂′ ⊔ ℓ₂′ ⊔ e₂′ ⊔ cs ⊔ ℓs) where
    field
      effect : GradedKleisliMorphism S.ℳ S′.ℳ

    open GradedKleisliMorphism effect public

    field
      ν : PresheafMorphism F S.ℰ S′.ℰ

    module ν = PresheafMorphism ν

-- Keeping 𝒞, ℐ and ℳ and replacing ℰ by a presheaf that receives ℰ's tests
module _ {𝒞 : Category o₁′ ℓ₁′ e₁′} {ℐ : MonoidalCategory o₁ ℓ₁ e₁}
         {ℳ : GradedKleisliTriple ℐ 𝒞}
         (ℰ ℰ′ : Presheaf 𝒞 (Setoids cs ℓs)) where

  changeKernel : PresheafMorphism idF ℰ ℰ′
               → UCSetupMorphism (record { 𝒞 = 𝒞 ; ℐ = ℐ ; ℳ = ℳ ; ℰ = ℰ })
                                 (record { 𝒞 = 𝒞 ; ℐ = ℐ ; ℳ = ℳ ; ℰ = ℰ′ })
  changeKernel ν = record { effect = idMorphism 𝒞 ℐ ℳ ; ν = ν }

------------------------------------------------------------------------
-- Identity and composition
------------------------------------------------------------------------

idᵁ : (𝕊 : UCSetup o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ cs ℓs) → UCSetupMorphism 𝕊 𝕊
idᵁ 𝕊 = changeKernel ℰ ℰ (idᵛ ℰ)
  where open UCSetup 𝕊

module _ {𝕊 : UCSetup o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ cs ℓs}
         {𝕊′ : UCSetup o₂ ℓ₂ e₂ o₂′ ℓ₂′ e₂′ cs ℓs}
         {𝕊″ : UCSetup o₃ ℓ₃ e₃ o₃′ ℓ₃′ e₃′ cs ℓs} where

  composeᵁ : UCSetupMorphism 𝕊′ 𝕊″ → UCSetupMorphism 𝕊 𝕊′ → UCSetupMorphism 𝕊 𝕊″
  composeᵁ 𝕄′ 𝕄 = record
    { effect = composeMorphism 𝕄′.effect 𝕄.effect
    ; ν = _∘ᵛ_ {G = 𝕄.F} {F = 𝕄′.F} 𝕄′.ν 𝕄.ν }
    where module 𝕄 = UCSetupMorphism 𝕄
          module 𝕄′ = UCSetupMorphism 𝕄′

module _ {𝕊 : UCSetup o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ cs ℓs}
         {𝕊′ : UCSetup o₂ ℓ₂ e₂ o₂′ ℓ₂′ e₂′ cs ℓs}
         (𝕄 : UCSetupMorphism 𝕊 𝕊′) where
  private
    module S′ = UCSetup 𝕊′
    module 𝕄 = UCSetupMorphism 𝕄
    module 𝕄∘id = UCSetupMorphism (composeᵁ 𝕄 (idᵁ 𝕊))
    module id∘𝕄 = UCSetupMorphism (composeᵁ (idᵁ 𝕊′) 𝕄)
    module ℰ = Functor (UCSetup.ℰ 𝕊)
    module ℰ′ {A} = Setoid (Functor.₀ S′.ℰ (𝕄.F.₀ A))

  identityʳ-κ : ∀ {X A} → 𝕄∘id.κ {X} {A} S′.𝒞.≈ 𝕄.κ
  identityʳ-κ = S′.𝒞.elimʳ 𝕄.F.identity

  identityˡ-κ : ∀ {X A} → id∘𝕄.κ {X} {A} S′.𝒞.≈ 𝕄.κ
  identityˡ-κ = S′.𝒞.identityˡ

  identityʳ-ν : ∀ {A} {x : Setoid.Carrier (ℰ.₀ A)}
              → 𝕄∘id.ν.η A ⟨$⟩ x ℰ′.≈ 𝕄.ν.η A ⟨$⟩ x
  identityʳ-ν = ℰ′.refl

  identityˡ-ν : ∀ {A} {x : Setoid.Carrier (ℰ.₀ A)}
              → id∘𝕄.ν.η A ⟨$⟩ x ℰ′.≈ 𝕄.ν.η A ⟨$⟩ x
  identityˡ-ν = ℰ′.refl

------------------------------------------------------------------------
-- The epi/mono factorization
------------------------------------------------------------------------

module Factorization {𝕊 : UCSetup o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ cs ℓs}
                     {𝕊′ : UCSetup o₂ ℓ₂ e₂ o₂′ ℓ₂′ e₂′ cs ℓs}
                     (𝕄 : UCSetupMorphism 𝕊 𝕊′) where
  open UCSetupMorphism 𝕄

  imageSetup : UCSetup o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ cs ℓs
  imageSetup = record
    { 𝒞 = UCSetup.𝒞 𝕊 ; ℐ = UCSetup.ℐ 𝕊 ; ℳ = UCSetup.ℳ 𝕊 ; ℰ = image ν }

  coarsen-to-image : UCSetupMorphism 𝕊 imageSetup
  coarsen-to-image = changeKernel (UCSetup.ℰ 𝕊) (image ν) (toImage ν)

  image-morphism : UCSetupMorphism imageSetup 𝕊′
  image-morphism = record { effect = effect ; ν = fromImage ν }
