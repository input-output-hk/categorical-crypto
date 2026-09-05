{-# OPTIONS --safe --without-K --guardedness #-}

-- The cast at the shape `associator.isoʳ` is stated at; see
-- `UC.Machine.Cast.Tensor` for why the factors are variable and why one shape
-- gets one module.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚᴹ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ)

module CategoricalCrypto.UC.Machine.Cast.Assoc where

private
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

∘ᴳ-α : (X Y A : Iface)
       (g : Proc ((X ⊗ᴵ Y) ⊗ᴵ A) (X ⊗ᴵ (Y ⊗ᴵ A)))
       (f : Proc (X ⊗ᴵ (Y ⊗ᴵ A)) ((X ⊗ᴵ Y) ⊗ᴵ A))
     → 𝒫._≈_ {X ⊗ᴵ (Y ⊗ᴵ A)} {X ⊗ᴵ (Y ⊗ᴵ A)}
         (𝒫._∘_ {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ A} {X ⊗ᴵ (Y ⊗ᴵ A)} g f)
         (𝔾._∘_ {𝔾._⊗₀_ ⟦ X ⟧ᴵ (𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ A ⟧ᴵ)}
                {𝔾._⊗₀_ (𝔾._⊗₀_ ⟦ X ⟧ᴵ ⟦ Y ⟧ᴵ) ⟦ A ⟧ᴵ}
                {𝔾._⊗₀_ ⟦ X ⟧ᴵ (𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ A ⟧ᴵ)} g f)
∘ᴳ-α X Y A g f = 𝒫.Equiv.refl {X ⊗ᴵ (Y ⊗ᴵ A)} {X ⊗ᴵ (Y ⊗ᴵ A)}
