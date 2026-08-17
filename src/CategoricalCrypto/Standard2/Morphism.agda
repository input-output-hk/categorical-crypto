{-# OPTIONS --safe --without-K #-}

-- Morphisms between standard setups

module CategoricalCrypto.Standard2.Morphism where

open import Level

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Reasoning as MonoidalR
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties.Ext
open import Categories.Functor.Presheaf
open import Categories.Functor.Presheaf.Morphism
import Categories.Morphism.Reasoning as MR

open import CategoricalCrypto.Standard2
open import CategoricalCrypto.UCSetup.Morphism

module _ {o ℓ e o′ ℓ′ e′ cs ℓs : Level}
         (𝕄 : MonoidalCategory o ℓ e) (𝕄′ : MonoidalCategory o′ ℓ′ e′)
         (ℰ : Presheaf (MonoidalCategory.U 𝕄) (Setoids cs ℓs))
         (ℰ′ : Presheaf (MonoidalCategory.U 𝕄′) (Setoids cs ℓs))
         (F : StrongMonoidalFunctor 𝕄 𝕄′) where
  private
    module S = StdUC 𝕄 ℰ
    module S′ = StdUC 𝕄′ ℰ′
    module F = StrongMonoidalFunctor F
    module Op = Oplax F
  open MonoidalCategory 𝕄′
  open MonoidalR monoidal
  open MonoidalUtilities.Shorthands monoidal
  open MR U

  StdUCMorphism : PresheafMorphism F.F ℰ ℰ′
                → UCSetupMorphism S.StdSetup S′.StdSetup
  StdUCMorphism ν = record
    { effect = record
      { F = F.F ; Φ = F.monoidalFunctor ; κ = Op.δ
      ; isGradedKleisliMorphism = record
        { κ-return = Op.δ-unitorˡ
        ; κ-sub    = Op.δ-commuteʳ
        ; κ-ext    = ext-law
        }
      }
    ; ν = ν
    }
    where
      ext-law : ∀ {X Y A B} (f : A S.⇒ S.T₀ Y B)
              → Op.δ ∘ F.₁ (S.ext X f)
                ≈ (Op.ψ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (Op.δ ∘ F.₁ f))) ∘ Op.δ
      ext-law f = (refl⟩∘⟨ F.homomorphism) ○ extendʳ Op.δ-assoc′
                ○ (refl⟩∘⟨ Op.δ-commuteˡ f) ○ center (pullʳ merge₂ʳ)
