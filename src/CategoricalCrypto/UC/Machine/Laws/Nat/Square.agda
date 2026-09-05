{-# OPTIONS --safe --without-K --guardedness #-}

-- `assoc-commute-to` at `id , id , f`, re-spelled in the vocabulary
-- `UC.Machine.Laws.Nat` can name.
--
-- The re-spelling is what costs: a 𝒢-composite whose two sides are not
-- SYNTACTICALLY equal is compared by reducing both to the ⊕-trace, ~400 s a
-- time, and `Monoidal`'s own statement is one δ away on every leaf (its `α⇐`
-- and `_⊗₁_` are the record's private abbreviations, unwritable here).  The
-- square has two such sides, which is one more than a module can afford under
-- `pagda`'s 900 s cap — so it gets a module of its own and
-- `UC.Machine.Laws.Nat` then chains four steps whose junctions are all
-- syntactic.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚᴹ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ)

module CategoricalCrypto.UC.Machine.Laws.Nat.Square where

private
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

α-natᴳ : (X Y A B : Iface) (f : Proc A B)
       → 𝔾._≈_ {𝔾._⊗₀_ ⟦ X ⟧ᴵ (𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ A ⟧ᴵ)}
               {𝔾._⊗₀_ (𝔾._⊗₀_ ⟦ X ⟧ᴵ ⟦ Y ⟧ᴵ) ⟦ B ⟧ᴵ}
           (𝔾._∘_ {𝔾._⊗₀_ ⟦ X ⟧ᴵ (𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ A ⟧ᴵ)}
                  {𝔾._⊗₀_ ⟦ X ⟧ᴵ (𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ B ⟧ᴵ)}
                  {𝔾._⊗₀_ (𝔾._⊗₀_ ⟦ X ⟧ᴵ ⟦ Y ⟧ᴵ) ⟦ B ⟧ᴵ}
              (𝔾.associator.to {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ B ⟧ᴵ})
              (𝔾._⊗₁_ {⟦ X ⟧ᴵ} {⟦ X ⟧ᴵ}
                      {𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ A ⟧ᴵ} {𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ B ⟧ᴵ}
                 (𝒫.id {X})
                 (𝔾._⊗₁_ {⟦ Y ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} (𝒫.id {Y}) f)))
           (𝔾._∘_ {𝔾._⊗₀_ ⟦ X ⟧ᴵ (𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ A ⟧ᴵ)}
                  {𝔾._⊗₀_ (𝔾._⊗₀_ ⟦ X ⟧ᴵ ⟦ Y ⟧ᴵ) ⟦ A ⟧ᴵ}
                  {𝔾._⊗₀_ (𝔾._⊗₀_ ⟦ X ⟧ᴵ ⟦ Y ⟧ᴵ) ⟦ B ⟧ᴵ}
              (𝔾._⊗₁_ {𝔾._⊗₀_ ⟦ X ⟧ᴵ ⟦ Y ⟧ᴵ} {𝔾._⊗₀_ ⟦ X ⟧ᴵ ⟦ Y ⟧ᴵ}
                      {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ}
                 (𝔾._⊗₁_ {⟦ X ⟧ᴵ} {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ Y ⟧ᴵ}
                    (𝒫.id {X}) (𝒫.id {Y}))
                 f)
              (𝔾.associator.to {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ}))
α-natᴳ X Y A B f = 𝔾.assoc-commute-to {f = 𝒫.id {X}} {g = 𝒫.id {Y}} {h = f}
