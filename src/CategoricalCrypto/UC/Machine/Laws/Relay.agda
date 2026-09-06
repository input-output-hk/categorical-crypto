{-# OPTIONS --safe --without-K --guardedness #-}

-- `GradingLawsᴹ.T₁-∘`, from `⊗.homomorphism`.
--
-- Each of the four is the same three-step shape: `UC.Machine.Dictionary` reads
-- the relay as its monoidal spelling, a `UC.Machine.Cast.*` lemma reads the
-- `𝒫ᴵ`-composite as the 𝒢-composite at the spelling the borrowed law states,
-- and the law applies.  Every implicit is pinned, both this layer's objects and
-- the borrowed law's own (`UC.Machine.Dictionary`'s header prices leaving
-- either to inference); one law per module for the reason
-- `UC.Machine.Cast.Tensor` records — a module affords one 𝒢-composite
-- conversion, which is the junction against the borrowed law.  Measured warm:
-- 489 s.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Product.Base using (_,_)
open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚᴹ; 𝒱ₚ; 𝒫ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Cast.Tensor
open import CategoricalCrypto.UC.Machine.Dictionary

import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Laws.Relay where

private
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

-- The bifunctor's law composes BOTH factors, so the ancilla side arrives as
-- `id ∘ id` and `identity²` is what puts it back.
T₁-∘ᴹ : {Y A B C : Iface} {g : Proc B C} {f : Proc A B}
      → 𝒫._≈_ {Y ⊗ᴵ A} {Y ⊗ᴵ C}
          (T₁ᴵ Y {A} {C} (𝒫._∘_ {A} {B} {C} g f))
          (𝒫._∘_ {Y ⊗ᴵ A} {Y ⊗ᴵ B} {Y ⊗ᴵ C} (T₁ᴵ Y {B} {C} g) (T₁ᴵ Y {A} {B} f))
T₁-∘ᴹ {Y} {A} {B} {C} {g} {f} =
     T₁-⊗₁ {Y} {A} {C} (𝒫._∘_ {A} {B} {C} g f)
  ○ᴹ 𝔾.⊗.F-resp-≈ {⟦ Y ⟧ᴵ , ⟦ A ⟧ᴵ} {⟦ Y ⟧ᴵ , ⟦ C ⟧ᴵ}
       {𝒫.id {Y} , 𝒫._∘_ {A} {B} {C} g f}
       {𝒫._∘_ {Y} {Y} {Y} (𝒫.id {Y}) (𝒫.id {Y}) , 𝒫._∘_ {A} {B} {C} g f}
       (𝒫.Equiv.sym {Y} {Y} (𝒫.identity² {Y})
       , 𝔾.Equiv.refl {x = 𝒫._∘_ {A} {B} {C} g f})
  ○ᴹ 𝔾.⊗.homomorphism {⟦ Y ⟧ᴵ , ⟦ A ⟧ᴵ} {⟦ Y ⟧ᴵ , ⟦ B ⟧ᴵ} {⟦ Y ⟧ᴵ , ⟦ C ⟧ᴵ}
       {𝒫.id {Y} , f} {𝒫.id {Y} , g}
  ○ᴹ ⟺ᴹ (∘ᴳ-T₁ Y A B C
           (𝔾._⊗₁_ {⟦ Y ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ B ⟧ᴵ} {⟦ C ⟧ᴵ} (𝒫.id {Y}) g)
           (𝔾._⊗₁_ {⟦ Y ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} (𝒫.id {Y}) f))
  ○ᴹ 𝒫.∘-resp-≈ {Y ⊗ᴵ A} {Y ⊗ᴵ B} {Y ⊗ᴵ C}
       (⟺ᴹ (T₁-⊗₁ {Y} {B} {C} g)) (⟺ᴹ (T₁-⊗₁ {Y} {A} {B} f))
