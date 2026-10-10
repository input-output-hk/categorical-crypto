{-# OPTIONS --safe --without-K #-}

-- Wires along container maps.  `⌜_⌝` is functorial: wires compose and tensor
-- as their container maps do, contravariantly in composition, each law one
-- stateless simulation whose two step trees are the same call.
-- `interchangeᴵ` is the middle-four interchange of a tensor of tensors.

open import Data.Sum.Base using (inj₁; inj₂)

open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol

module CategoricalCrypto.SSP.Protocol.Wire where

private variable A B C D : Iface

⌜⌝-∘ : (m : B ⇒ᴵ C) (n : A ⇒ᴵ B) → ⌜ n ⌝ ∘ᵖ ⌜ m ⌝ ≈ᵖ ⌜ m ∘ᴵ n ⌝
⌜⌝-∘ m n = ≲⇒≈ᵖ (≲ᵖ-const λ _ _ _ → ≈ᶜ-refl)

⌜⌝-⊗ : (m : A ⇒ᴵ B) (n : C ⇒ᴵ D) → ⌜ m ⌝ ⊗ᵖ ⌜ n ⌝ ≈ᵖ ⌜ m ⊗ᴵᴵ n ⌝
⌜⌝-⊗ m n = ≲⇒≈ᵖ (≲ᵖ-const λ where
  _ (inj₁ _) _ → ≈ᶜ-refl
  _ (inj₂ _) _ → ≈ᶜ-refl)

interchangeᴵ : (A ⊗ᴵ B) ⊗ᴵ (C ⊗ᴵ D) ⇒ᴵ (A ⊗ᴵ C) ⊗ᴵ (B ⊗ᴵ D)
interchangeᴵ = αᴵ⁻¹ ∘ᴵ (idᴵ ⊗ᴵᴵ (αᴵ ∘ᴵ (swapᴵ ⊗ᴵᴵ idᴵ) ∘ᴵ αᴵ⁻¹)) ∘ᴵ αᴵ
