{-# OPTIONS --safe --without-K #-}

open import Level

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Monad.Graded

module Categories.Monad.Graded.Ext
  {o ℓ e o′ ℓ′ e′ : Level} {ℐ : MonoidalCategory o ℓ e} {𝒞 : Category o′ ℓ′ e′}
  (ℳ : GradedKleisliTriple ℐ 𝒞) where

import Categories.Morphism.Reasoning as MR

open Category 𝒞
open GradedKleisliTriple ℳ
open HomReasoning
open MR 𝒞

private module ℐ = MonoidalCategory ℐ

sub-identityˡ : ∀ {u A B} (f : B ⇒ T₀ u A) → sub ℐ.id ∘ f ≈ f
sub-identityˡ _ = elimˡ sub-identity

μT : ∀ {u v A B} (f : A ⇒ T₀ v B) → μ u v ∘ T₁ u f ≈ ext u f
μT _ = ext-T-fusion ○ ext-resp-≈ identityˡ
