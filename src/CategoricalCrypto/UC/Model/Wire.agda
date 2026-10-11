{-# OPTIONS --safe --without-K --guardedness #-}

-- `𝔾ˢ` at interface objects.  Under the seal `ifaceᵒ` is strict monoidal on the
-- nose (`UC.Model.Seal.⊗ᵒ`); outside it the comparisons are the isos `⊗ᵒ≅` and
-- `𝟭ᵒ≅`, identities under the seal, and `procᵒ` carries `UC.Machine`'s tensor
-- of processes to `𝔾ᵒ`'s through them (`procᵒ-⊗`).  Every structural map of
-- `𝔾ˢ` at interfaces is a wire conjugated by the comparisons — the dictionary
-- (`UC.Machine.Dictionary`) read across the seal — so a composite of
-- structural maps and processes at interfaces is `procᵒ` of a composite of
-- processes, which the wire algebra (`UC.Machine.Wire.Algebra`) compares.
-- Nothing here opens `StdUC` (`UC.Model.Enrichment`'s header).

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle
import Categories.Morphism as Mor

open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂; swap)
open import Level

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pure using (swapᵏ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Symmetric

import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Model.Wire where

private
  module G = SymmetricMonoidalCategory 𝔾ˢ
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

open Mor G.U
open G.HomReasoning

private variable A B C D : Iface

opaque
  unfolding 𝔾ᵒ ifaceᵒ procᵒ symmetricᵒ

  ⊗ᵒ≅ : (A B : Iface) → ifaceᵒ A G.⊗₀ ifaceᵒ B ≅ ifaceᵒ (A ⊗ᴵ B)
  ⊗ᵒ≅ _ _ = ≅.refl

  -- `𝟭ᴵ` is the bundle's own unit read as an interface (`UC.Machine.Dictionary`).
  𝟭ᵒ≅ : G.unit ≅ ifaceᵒ 𝟭ᴵ
  𝟭ᵒ≅ = ≅.refl

  procᵒ-id : procᵒ (𝒫.id {A}) G.≈ G.id
  procᵒ-id = S.reflᴹ

  procᵒ-⊗ : (f : Proc A B) (g : Proc C D)
          → procᵒ (𝔾._⊗₁_ {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} {⟦ C ⟧ᴵ} {⟦ D ⟧ᴵ} f g)
            G.≈ _≅_.from (⊗ᵒ≅ B D) G.∘ (procᵒ f G.⊗₁ procᵒ g) G.∘ _≅_.to (⊗ᵒ≅ A C)
  procᵒ-⊗ _ _ = ⟺ (G.identityˡ ○ G.identityʳ)

  private
    -- Under the seal every comparison is an identity.
    trim : {f : ifaceᵒ A G.⇒ ifaceᵒ B} → G.id G.∘ f G.∘ G.id G.≈ f
    trim = G.identityˡ ○ G.identityʳ

  λ-wireᵒ : G.unitorˡ.from {ifaceᵒ A} G.≈ procᵒ (λᴵ {A}) G.∘ _≅_.from (⊗ᵒ≅ 𝟭ᴵ A) G.∘ (_≅_.from 𝟭ᵒ≅ G.⊗₁ G.id)
  λ-wireᵒ = S.⟺ᴹ λ⇒-λᴳ ○ ⟺ ((refl⟩∘⟨ (G.identityˡ ○ G.⊗.identity)) ○ G.identityʳ)

  λ⇐-wireᵒ : G.unitorˡ.to {ifaceᵒ A}
           G.≈ (_≅_.to 𝟭ᵒ≅ G.⊗₁ G.id) G.∘ _≅_.to (⊗ᵒ≅ 𝟭ᴵ A) G.∘ procᵒ (wireᴹ {A} {𝟭ᴵ ⊗ᴵ A} inj₂ drop⇒ˡ)
  λ⇐-wireᵒ = S.⟺ᴹ λ⇐-λᴳ ○ ⟺ (G.⊗.identity ⟩∘⟨refl ○ G.identityˡ ○ G.identityˡ)

  ρ-wireᵒ : G.unitorʳ.from {ifaceᵒ A}
          G.≈ procᵒ (wireᴹ {A ⊗ᴵ 𝟭ᴵ} {A} drop⇒ʳ inj₁) G.∘ _≅_.from (⊗ᵒ≅ A 𝟭ᴵ) G.∘ (G.id G.⊗₁ _≅_.from 𝟭ᵒ≅)
  ρ-wireᵒ = S.⟺ᴹ ρ⇒-ρᴳ ○ ⟺ ((refl⟩∘⟨ (G.identityˡ ○ G.⊗.identity)) ○ G.identityʳ)

  ρ⇐-wireᵒ : G.unitorʳ.to {ifaceᵒ A}
           G.≈ (G.id G.⊗₁ _≅_.to 𝟭ᵒ≅) G.∘ _≅_.to (⊗ᵒ≅ A 𝟭ᴵ) G.∘ procᵒ (wireᴹ {A} {A ⊗ᴵ 𝟭ᴵ} inj₁ drop⇒ʳ)
  ρ⇐-wireᵒ = S.⟺ᴹ ρ⇐-ρᴳ ○ ⟺ (G.⊗.identity ⟩∘⟨refl ○ G.identityˡ ○ G.identityˡ)

  α-wireᵒ : G.associator.from {ifaceᵒ A} {ifaceᵒ B} {ifaceᵒ C}
          G.≈ (G.id G.⊗₁ _≅_.to (⊗ᵒ≅ B C)) G.∘ _≅_.to (⊗ᵒ≅ A (B ⊗ᴵ C)) G.∘ procᵒ (a⇒ᴵ {A} {B} {C})
              G.∘ _≅_.from (⊗ᵒ≅ (A ⊗ᴵ B) C) G.∘ (_≅_.from (⊗ᵒ≅ A B) G.⊗₁ G.id)
  α-wireᵒ = S.⟺ᴹ a⇒-α⇒ ○ ⟺ ((G.⊗.identity ⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ G.⊗.identity)
                              ○ G.identityˡ ○ G.identityˡ ○ (refl⟩∘⟨ G.identityˡ) ○ G.identityʳ)

  α⇐-wireᵒ : G.associator.to {ifaceᵒ A} {ifaceᵒ B} {ifaceᵒ C}
           G.≈ (_≅_.to (⊗ᵒ≅ A B) G.⊗₁ G.id) G.∘ _≅_.to (⊗ᵒ≅ (A ⊗ᴵ B) C) G.∘ procᵒ (a⇐ᴵ {A} {B} {C})
               G.∘ _≅_.from (⊗ᵒ≅ A (B ⊗ᴵ C)) G.∘ (G.id G.⊗₁ _≅_.from (⊗ᵒ≅ B C))
  α⇐-wireᵒ = S.⟺ᴹ a⇐-α⇐ ○ ⟺ ((G.⊗.identity ⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ G.⊗.identity)
                               ○ G.identityˡ ○ G.identityˡ ○ (refl⟩∘⟨ G.identityˡ) ○ G.identityʳ)

  σ-wireᵒ : G.braiding.⇒.η (ifaceᵒ A , ifaceᵒ B)
          G.≈ _≅_.to (⊗ᵒ≅ B A) G.∘ procᵒ (wireᴹ {A ⊗ᴵ B} {B ⊗ᴵ A} swap swap) G.∘ _≅_.from (⊗ᵒ≅ A B)
  σ-wireᵒ = S.⟺ᴹ (wire-pure swap swap _ _ swapᵏ swapᵏ) ○ ⟺ trim

-- An iso of processes at interfaces is an iso of `𝔾ᵒ`.
procᵒ-≅ : (f : Proc A B) (g : Proc B A)
        → 𝒫._≈_ {A} {A} (g 𝒫.∘ f) (𝒫.id {A}) → 𝒫._≈_ {B} {B} (f 𝒫.∘ g) (𝒫.id {B}) → ifaceᵒ A ≅ ifaceᵒ B
procᵒ-≅ f g gf fg = record
  { from = procᵒ f
  ; to   = procᵒ g
  ; iso  = record
    { isoˡ = ⟺ (procᵒ-∘ g f) ○ ≈ᴹ⇒≈ᵒ gf ○ procᵒ-id
    ; isoʳ = ⟺ (procᵒ-∘ f g) ○ ≈ᴹ⇒≈ᵒ fg ○ procᵒ-id
    }
  }
