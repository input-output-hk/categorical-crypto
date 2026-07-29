{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.UCSetup where

open import Data.Product
open import Level
open import Relation.Binary.Bundles
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Functor.Presheaf
import Categories.KernelCongruence as KernelCong
open import Categories.LocallyGraded
import Categories.LocallyGraded.Kleisli as LGKleisli
open import Categories.Monad.Graded
import Categories.Morphism.Reasoning as MR

record UCSetup (o ℓ e o′ ℓ′ e′ cs ℓs : Level) : Set (suc (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ cs ⊔ ℓs)) where
  field
    𝒞 : Category o′ ℓ′ e′
    ℐ : MonoidalCategory o ℓ e
    ℳ : GradedKleisliTriple ℐ 𝒞
    ℰ : Presheaf 𝒞 (Setoids cs ℓs)

  module 𝒞 where
    open Category 𝒞 public
    open HomReasoning public
    open MR 𝒞 public
  module ℐ = MonoidalCategory ℐ
  open GradedKleisliTriple ℳ public
  open import Categories.Category.Monoidal.Utilities ℐ.monoidal public
  open Shorthands public

  open ℐ using (_⊗₀_; _⊗₁_) public
