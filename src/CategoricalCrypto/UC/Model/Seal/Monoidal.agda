{-# OPTIONS --safe --without-K --guardedness #-}

-- Separate coercions keep the sealed tensor's endpoints nominal; unfolding
-- a UC setup to identify them would expand the whole machine bundle.

open import Categories.Category.Monoidal.Bundle
open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Tensor
open import CategoricalCrypto.UC.Model.Seal

import CategoricalCrypto.Machines.Sim as Sim
open import CategoricalCrypto.Machines.Base
open import Level using (0ℓ)

module CategoricalCrypto.UC.Model.Seal.Monoidal where

private
  module G = MonoidalCategory 𝔾ᵒ
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

opaque
  unfolding 𝔾ᵒ ifaceᵒ procᵒ

  tensorᵒ : {A B C D : Iface} → Proc (A ⊗ᴵ C) (B ⊗ᴵ D)
           → (ifaceᵒ A G.⊗₀ ifaceᵒ C) G.⇒ (ifaceᵒ B G.⊗₀ ifaceᵒ D)
  tensorᵒ f = f

  untensorᵒ : {A B C D : Iface}
             → (ifaceᵒ A G.⊗₀ ifaceᵒ C) G.⇒ (ifaceᵒ B G.⊗₀ ifaceᵒ D)
             → Proc (A ⊗ᴵ C) (B ⊗ᴵ D)
  untensorᵒ f = f

  ≈ᴹ⇒≈⊗ᵒ : {A B C D : Iface} {f g : Proc (A ⊗ᴵ C) (B ⊗ᴵ D)}
           → f S.≈ᴹ g → tensorᵒ f G.≈ tensorᵒ g
  ≈ᴹ⇒≈⊗ᵒ e = e

  ≈⊗ᵒ⇒≈ᴹ : {A B C D : Iface}
            {f g : (ifaceᵒ A G.⊗₀ ifaceᵒ C) G.⇒ (ifaceᵒ B G.⊗₀ ifaceᵒ D)}
          → f G.≈ g → untensorᵒ f S.≈ᴹ untensorᵒ g
  ≈⊗ᵒ⇒≈ᴹ e = e

  procᵒ-tensor : {A B C D : Iface} (f : Proc A B) (g : Proc C D)
               → (procᵒ f G.⊗₁ procᵒ g) G.≈ tensorᵒ (tensorᴹ f g)
  procᵒ-tensor f g = S.⟺ᴹ (tensor-correct f g)
