{-# OPTIONS --safe --without-K --guardedness #-}

-- `GradingLawsᴹ.sub-∘`, from `⊗.homomorphism`.
--
-- Each of the four is the same three-step shape: `UC.Machine.Dictionary` reads
-- the relay as its monoidal spelling, a `UC.Machine.Cast.*` lemma reads the
-- `𝒫ᴵ`-composite as the 𝒢-composite at the spelling the borrowed law states,
-- and the law applies.  Every implicit is pinned, both this layer's objects and
-- the borrowed law's own (`UC.Machine.Dictionary`'s header prices leaving
-- either to inference); one law per module for the reason
-- `UC.Machine.Cast.Tensor` records — a module affords one 𝒢-composite
-- conversion, which is the junction against the borrowed law.  Measured warm:
-- 495 s.

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

module CategoricalCrypto.UC.Machine.Laws.Simulator where

private
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

sub-∘ᴹ : {X Y Z A : Iface} {t : Proc Y Z} {s : Proc X Y}
       → 𝒫._≈_ {X ⊗ᴵ A} {Z ⊗ᴵ A}
           (subᴵ′ {X} {Z} {A} (𝒫._∘_ {X} {Y} {Z} t s))
           (𝒫._∘_ {X ⊗ᴵ A} {Y ⊗ᴵ A} {Z ⊗ᴵ A}
              (subᴵ′ {Y} {Z} {A} t) (subᴵ′ {X} {Y} {A} s))
sub-∘ᴹ {X} {Y} {Z} {A} {t} {s} =
     sub-⊗₁ {X} {Z} {A} (𝒫._∘_ {X} {Y} {Z} t s)
  ○ᴹ 𝔾.⊗.F-resp-≈ {⟦ X ⟧ᴵ , ⟦ A ⟧ᴵ} {⟦ Z ⟧ᴵ , ⟦ A ⟧ᴵ}
       {𝒫._∘_ {X} {Y} {Z} t s , 𝒫.id {A}}
       {𝒫._∘_ {X} {Y} {Z} t s , 𝒫._∘_ {A} {A} {A} (𝒫.id {A}) (𝒫.id {A})}
       (𝔾.Equiv.refl {x = 𝒫._∘_ {X} {Y} {Z} t s}
       , 𝒫.Equiv.sym {A} {A} (𝒫.identity² {A}))
  ○ᴹ 𝔾.⊗.homomorphism {⟦ X ⟧ᴵ , ⟦ A ⟧ᴵ} {⟦ Y ⟧ᴵ , ⟦ A ⟧ᴵ} {⟦ Z ⟧ᴵ , ⟦ A ⟧ᴵ}
       {s , 𝒫.id {A}} {t , 𝒫.id {A}}
  ○ᴹ ⟺ᴹ (∘ᴳ-sub X Y Z A
           (𝔾._⊗₁_ {⟦ Y ⟧ᴵ} {⟦ Z ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ A ⟧ᴵ} t (𝒫.id {A}))
           (𝔾._⊗₁_ {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ A ⟧ᴵ} s (𝒫.id {A})))
  ○ᴹ 𝒫.∘-resp-≈ {X ⊗ᴵ A} {Y ⊗ᴵ A} {Z ⊗ᴵ A}
       (⟺ᴹ (sub-⊗₁ {Y} {Z} {A} t)) (⟺ᴹ (sub-⊗₁ {X} {Y} {A} s))
