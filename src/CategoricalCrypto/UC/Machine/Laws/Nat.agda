{-# OPTIONS --safe --without-K --guardedness #-}

-- `GradingLawsᴹ.a-nat`, from `assoc-commute-to`.
--
-- Each of the four is the same three-step shape: `UC.Machine.Dictionary` reads
-- the relay as its monoidal spelling, a `UC.Machine.Cast.*` lemma reads the
-- `𝒫ᴵ`-composite as the 𝒢-composite at the spelling the borrowed law states,
-- and the law applies.  Every implicit is pinned, both this layer's objects and
-- the borrowed law's own (`UC.Machine.Dictionary`'s header prices leaving
-- either to inference); one law per module for the reason
-- `UC.Machine.Cast.Tensor` records.  This one takes the borrowed law
-- pre-spelled from `…Laws.Nat.Square`, so that every junction below is
-- syntactic and the module carries no 𝒢-composite conversion at all.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Product.Base using (_,_)
open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚᴹ; 𝒱ₚ; 𝒫ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Cast.Nat
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Laws.Nat.Square

import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Laws.Nat where

private
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

-- The square is at `f , g , h := id , id , f`; the `(id ⊗₁ id) ⊗₁ f` it leaves
-- on the right is `⊗.identity` away from `T₁ᴵ (X ⊗ᴵ Y) f`.
a-natᴹ : {X Y A B : Iface} {f : Proc A B}
       → 𝒫._≈_ {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ B}
           (𝒫._∘_ {X ⊗ᴵ (Y ⊗ᴵ A)} {X ⊗ᴵ (Y ⊗ᴵ B)} {(X ⊗ᴵ Y) ⊗ᴵ B}
              (a⇒ᴵ {X} {Y} {B})
              (T₁ᴵ X {Y ⊗ᴵ A} {Y ⊗ᴵ B} (T₁ᴵ Y {A} {B} f)))
           (𝒫._∘_ {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ A} {(X ⊗ᴵ Y) ⊗ᴵ B}
              (T₁ᴵ (X ⊗ᴵ Y) {A} {B} f) (a⇒ᴵ {X} {Y} {A}))
a-natᴹ {X} {Y} {A} {B} {f} =
     𝒫.∘-resp-≈ {X ⊗ᴵ (Y ⊗ᴵ A)} {X ⊗ᴵ (Y ⊗ᴵ B)} {(X ⊗ᴵ Y) ⊗ᴵ B}
       {h = 𝔾.associator.to {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ B ⟧ᴵ}}
       {i = 𝔾._⊗₁_ {⟦ X ⟧ᴵ} {⟦ X ⟧ᴵ}
                   {𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ A ⟧ᴵ} {𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ B ⟧ᴵ} (𝒫.id {X})
              (𝔾._⊗₁_ {⟦ Y ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} (𝒫.id {Y}) f)}
       (a⇒-α⇐ {X} {Y} {B})
       (   T₁-⊗₁ {X} {Y ⊗ᴵ A} {Y ⊗ᴵ B} (T₁ᴵ Y {A} {B} f)
        ○ᴹ 𝔾.⊗.F-resp-≈ {⟦ X ⟧ᴵ , 𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ A ⟧ᴵ}
                        {⟦ X ⟧ᴵ , 𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ B ⟧ᴵ}
             {𝒫.id {X} , T₁ᴵ Y {A} {B} f}
             {𝒫.id {X}
             , 𝔾._⊗₁_ {⟦ Y ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} (𝒫.id {Y}) f}
             (𝔾.Equiv.refl {x = 𝒫.id {X}} , T₁-⊗₁ {Y} {A} {B} f))
  ○ᴹ ∘ᴳ-nat⇒ X Y A B
       (𝔾.associator.to {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ B ⟧ᴵ})
       (𝔾._⊗₁_ {⟦ X ⟧ᴵ} {⟦ X ⟧ᴵ}
               {𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ A ⟧ᴵ} {𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ B ⟧ᴵ} (𝒫.id {X})
          (𝔾._⊗₁_ {⟦ Y ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} (𝒫.id {Y}) f))
  ○ᴹ α-natᴳ X Y A B f
  ○ᴹ ⟺ᴹ (∘ᴳ-nat⇐ X Y A B
           (𝔾._⊗₁_ {𝔾._⊗₀_ ⟦ X ⟧ᴵ ⟦ Y ⟧ᴵ} {𝔾._⊗₀_ ⟦ X ⟧ᴵ ⟦ Y ⟧ᴵ}
                   {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ}
              (𝔾._⊗₁_ {⟦ X ⟧ᴵ} {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ Y ⟧ᴵ} (𝒫.id {X}) (𝒫.id {Y}))
              f)
           (𝔾.associator.to {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ}))
  ○ᴹ 𝒫.∘-resp-≈ {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ A} {(X ⊗ᴵ Y) ⊗ᴵ B}
       (   𝔾.⊗.F-resp-≈ {𝔾._⊗₀_ ⟦ X ⟧ᴵ ⟦ Y ⟧ᴵ , ⟦ A ⟧ᴵ}
                        {𝔾._⊗₀_ ⟦ X ⟧ᴵ ⟦ Y ⟧ᴵ , ⟦ B ⟧ᴵ}
             {𝔾._⊗₁_ {⟦ X ⟧ᴵ} {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ Y ⟧ᴵ} (𝒫.id {X}) (𝒫.id {Y})
             , f}
             {𝒫.id {X ⊗ᴵ Y} , f}
             (𝔾.⊗.identity {⟦ X ⟧ᴵ , ⟦ Y ⟧ᴵ} , 𝔾.Equiv.refl {x = f})
        ○ᴹ ⟺ᴹ (T₁-⊗₁ {X ⊗ᴵ Y} {A} {B} f))
       (⟺ᴹ (a⇒-α⇐ {X} {Y} {A}))
