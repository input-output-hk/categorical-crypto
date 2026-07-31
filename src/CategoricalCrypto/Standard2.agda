{-# OPTIONS --safe --without-K #-}

-- The standard instantiation of the locally graded layer (Abstract2):
-- 𝒞 = ℐ = the monoidal category of machines

module CategoricalCrypto.Standard2 where

open import Level

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Functor.Monoidal.CurriedTensor
open import Categories.Functor.Presheaf
open import Categories.Monad.Graded

open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.UCSetup

module StdUC
  {o ℓ e cs ℓs : Level}
  (machines   : MonoidalCategory o ℓ e)
  (ℰ-standard : Presheaf (MonoidalCategory.U machines) (Setoids cs ℓs))
  where

  open MonoidalCategory machines renaming (U to ∣machines∣; Obj to Channel) public

  -- ℳ_X B = X ⊗ B, the curried tensor of the machine category
  ℳ-standard : GradedKleisliTriple machines ∣machines∣
  ℳ-standard = GradedMonad⇒GradedKleisliTriple (curriedTensor machines)

  StdSetup : UCSetup o ℓ e o ℓ e cs ℓs
  StdSetup = record { 𝒞 = ∣machines∣ ; ℐ = machines ; ℳ = ℳ-standard ; ℰ = ℰ-standard }

  open AbstractUC StdSetup hiding (_⊗₀_; _⊗₁_) public
