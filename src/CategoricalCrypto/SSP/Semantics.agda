{-# OPTIONS --safe --without-K --guardedness #-}

-- SSP compiled into PM[wb] (`docs/uc-setup-ssp.md` §4.3).  A protocol compiles
-- to a well-bracketed machine (`UC.Bracket.morphism-W`), hence to a map of
-- `𝒲ᴹ`, and compilation respects `≈ᵖ` and `∘ᵖ` already at `𝒲ᴹ`'s hom equality.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle

open import Data.Product.Base
open import Level

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Compose
open import CategoricalCrypto.Protocol.Machine.Resp
open import CategoricalCrypto.SSP.Compile
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Protocol.Category
open import CategoricalCrypto.UC.Bracket
open import CategoricalCrypto.UC.Bracket.Monoidal
open import CategoricalCrypto.UC.Bracket.Setup
open import CategoricalCrypto.UC.Bracket.Tensor
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Model.Seal

import Categories.Morphism as Mor
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.SSP.Semantics where

private
  module G  = MonoidalCategory 𝔾ᵒ
  module Gᴹ = Mor G.U
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝒫  = Category 𝒫ᴵ

private variable A B C : Iface

⟦_⟧ᵂ : Protocol A B → A 𝒲ᵂ.⇒ B
⟦_⟧ᵂ {A} P =
  procᵒ (morphism (toProtocol ⦃ Ch-dec A ⦄ P)) , morphism (toProtocol ⦃ Ch-dec A ⦄ P) , morphism-W ⦃ Ch-dec A ⦄ P
  , G.Equiv.refl

⟦⟧ᵂ-resp : {P P′ : Protocol A B} → P ≈ᵖ P′ → ⟦ P ⟧ᵂ 𝒲ᵂ.≈ ⟦ P′ ⟧ᵂ
⟦⟧ᵂ-resp {A} e = ≈ᴹ⇒≈ᵒ (morphism-resp (toProtocol-resp ⦃ Ch-dec A ⦄ e))

⟦⟧ᵂ-∘ : (P₂ : Protocol B C) (P₁ : Protocol A B) → ⟦ P₂ ∘ᵖ P₁ ⟧ᵂ 𝒲ᵂ.≈ ⟦ P₂ ⟧ᵂ 𝒲ᵂ.∘ ⟦ P₁ ⟧ᵂ
⟦⟧ᵂ-∘ {B} {A = A} P₂ P₁ = G.Equiv.trans
  (≈ᴹ⇒≈ᵒ (morphism-sim (toProtocol-∘ ⦃ Ch-dec A ⦄ ⦃ Ch-dec B ⦄ P₂ P₁) S.○ᴹ morphismCompose _ _)) (procᵒ-∘ _ _)

-- The compiled identity: the monitor of `docs/uc-setup-ssp.md` §4.3.
eᵂ : A 𝒲ᵂ.⇒ A
eᵂ = ⟦ wireᵖ ⟧ᵂ

eᵂ-idem : eᵂ {A} 𝒲ᵂ.∘ eᵂ {A} 𝒲ᵂ.≈ eᵂ {A}
eᵂ-idem {A} = G.Equiv.trans (G.Equiv.sym (⟦⟧ᵂ-∘ (wireᵖ {A}) (wireᵖ {A})))
  (⟦⟧ᵂ-resp (≲⇒≈ᵖ (wireᵖ-identityˡ (wireᵖ {A}))))

-- A map padded with identities and run against a closure is, as a hom of
-- `𝔾ᵒ`, the machine composite of the two witnesses.
pad∘ : {Y A B Z : Iface} (X : A 𝒲ᵂ.⇒ B) (c : unitᴵ 𝒲ᵂ.⇒ (Y ⊗ᴵ A) ⊗ᴵ Z)
     → proj₁ ((𝒲ᵂ.id {Y} 𝒲ᵂ.⊗₁ X) 𝒲ᵂ.⊗₁ 𝒲ᵂ.id {Z} 𝒲ᵂ.∘ c)
       G.≈ procᵒ (𝒫._∘_ {flat unitᴵ} {flat ((Y ⊗ᴵ A) ⊗ᴵ Z)} {flat ((Y ⊗ᴵ B) ⊗ᴵ Z)}
                    (_⊗ʷ_ {Y ⊗ᴵ A} {Y ⊗ᴵ B} {Z} {Z} (_⊗ʷ_ {Y} {Y} {A} {B} (𝒫.id {flat Y}) (proj₁ (proj₂ X)))
                          (𝒫.id {flat Z}))
                    (proj₁ (proj₂ c)))
pad∘ {Y} {A} {B} {Z} (x , x̂ , _ , ex) (c , ĉ , _ , ec) =
  G.∘-resp-≈ (refl⟩∘⟨ (G.⊗.F-resp-≈ (inner , procᵒ-id) ⟩∘⟨refl)) ec
  ○ (⊗-conj {Y ⊗ᴵ A} {Y ⊗ᴵ B} {Z} {Z} (_⊗ʷ_ {Y} {Y} {A} {B} (𝒫.id {flat Y}) x̂) (𝒫.id {flat Z}) ⟩∘⟨refl)
  ○ ⟺ (procᵒ-∘ {flat unitᴵ} {flat ((Y ⊗ᴵ A) ⊗ᴵ Z)} {flat ((Y ⊗ᴵ B) ⊗ᴵ Z)} _ ĉ)
  where
  open G.HomReasoning
  inner : Gᴹ._≅_.from (φ {Y} {B}) G.∘ (G.id G.⊗₁ x) G.∘ Gᴹ._≅_.to (φ {Y} {A}) G.≈ procᵒ (_⊗ʷ_ {Y} {Y} {A} {B} (𝒫.id {flat Y}) x̂)
  inner = (refl⟩∘⟨ (G.⊗.F-resp-≈ (procᵒ-id , ex) ⟩∘⟨refl)) ○ ⊗-conj {Y} {Y} {A} {B} (𝒫.id {flat Y}) x̂
