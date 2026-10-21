{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.Abstract2.Trace where

open import Data.Product
open import Level

open import Categories.Category.Monoidal

open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.UCSetup

module TraceUC
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level}
  (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs)
  (Monoidal-𝒞 : Monoidal (UCSetup.𝒞 setup))
  where
  open AbstractUC setup hiding (module 𝒞)
  module 𝒞 where
    open Monoidal Monoidal-𝒞 public
    open AbstractUC.𝒞 setup public

  private variable
    A B Z : 𝒞.Obj
    X Y : ℐ.Obj

  record TraceEffect : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      trace : A 𝒞.⊗₀ Z 𝒞.⇒ T₀ X (B 𝒞.⊗₀ Z) → A 𝒞.⇒ T₀ X B
      trace-sub : (s : Y ℐ.⇒ X) (f : A 𝒞.⊗₀ Z 𝒞.⇒ T₀ Y (B 𝒞.⊗₀ Z))
                → trace (sub s 𝒞.∘ f) 𝒞.≈ sub s 𝒞.∘ trace f

    TraceStable : Set (o ⊔ o′ ⊔ ℓ′ ⊔ cs ⊔ ℓs)
    TraceStable = ∀ {A B Z X} {f f′ : A 𝒞.⊗₀ Z 𝒞.⇒ T₀ X (B 𝒞.⊗₀ Z)}
                → f ≈ᵁ f′ → trace f ≈ᵁ trace f′

    UC-trace : TraceStable → ∀ {A B Z X Y}
      {f : A 𝒞.⊗₀ Z 𝒞.⇒ T₀ X (B 𝒞.⊗₀ Z)}
      {g : A 𝒞.⊗₀ Z 𝒞.⇒ T₀ Y (B 𝒞.⊗₀ Z)}
      → f ≤UC g → trace f ≤UC trace g
    UC-trace stable f≤g =
      let s , eq = ≤UC⇒dummy f≤g
      in dummy-complete (s , ≈ᵁ-trans (stable eq) (≈C⇒≈ᵁ (trace-sub s _)))
