{-# OPTIONS --safe --without-K --guardedness #-}

-- `GradingLawsᴹ.a-isoˡ`, from `associator.isoʳ`.
--
-- Each of the four is the same three-step shape: `UC.Machine.Dictionary` reads
-- the relay as its monoidal spelling, a `UC.Machine.Cast.*` lemma reads the
-- `𝒫ᴵ`-composite as the 𝒢-composite at the spelling the borrowed law states,
-- and the law applies.  Every implicit is pinned, both this layer's objects and
-- the borrowed law's own (`UC.Machine.Dictionary`'s header prices leaving
-- either to inference); one law per module for the reason
-- `UC.Machine.Cast.Tensor` records — a module affords one 𝒢-composite
-- conversion, which is the junction against the borrowed law.  Measured warm:
-- 423 s.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚᴹ; 𝒱ₚ; 𝒫ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Cast.Assoc
open import CategoricalCrypto.UC.Machine.Dictionary

import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Laws.Assoc where

private
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

a-isoˡᴹ : {X Y A : Iface}
        → 𝒫._≈_ {X ⊗ᴵ (Y ⊗ᴵ A)} {X ⊗ᴵ (Y ⊗ᴵ A)}
            (𝒫._∘_ {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ A} {X ⊗ᴵ (Y ⊗ᴵ A)}
               (a⇐ᴵ {X} {Y} {A}) (a⇒ᴵ {X} {Y} {A}))
            (𝒫.id {X ⊗ᴵ (Y ⊗ᴵ A)})
a-isoˡᴹ {X} {Y} {A} =
     𝒫.∘-resp-≈ {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ A} {X ⊗ᴵ (Y ⊗ᴵ A)}
       {h = 𝔾.associator.from {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ}}
       {i = 𝔾.associator.to {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ}}
       (a⇐-α⇒ {X} {Y} {A}) (a⇒-α⇐ {X} {Y} {A})
  ○ᴹ ∘ᴳ-α X Y A (𝔾.associator.from {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ})
                (𝔾.associator.to {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ})
  ○ᴹ 𝔾.associator.isoʳ {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ}
