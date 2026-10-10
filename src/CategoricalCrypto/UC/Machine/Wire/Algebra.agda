{-# OPTIONS --safe --without-K --guardedness #-}

-- Wires are closed under the layer's structure: a composite of two wires, a
-- relay of a wire and the identity are wires, so any structural composite is
-- one stateless relabelling, compared with another by its two functions.

open import Categories.Category

open import Data.Product.Base
open import Data.Sum.Base as Sum
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pure
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Wire

import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Wire.Algebra where

private
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

private variable A B C X Y : Iface

wire-cong : {up up′ : Pos A → Pos B} {down down′ : Neg B → Neg A}
          → (∀ p → up p ≡ up′ p) → (∀ n → down n ≡ down′ n)
          → 𝒫._≈_ {A} {B} (wireᴹ up down) (wireᴹ up′ down′)
wire-cong eu ed = S.≲⇒≈ᴹ (S.mk-cong λ where
  (s , inj₁ p) → ret≡ (cong (λ z → s , inj₂ z) (eu p))
  (s , inj₂ n) → ret≡ (cong (λ z → s , inj₁ z) (ed n)))

wire-id : 𝒫._≈_ {A} {A} (wireᴹ (λ p → p) (λ n → n)) (𝒫.id {A})
wire-id = S.≲⇒≈ᴹ (S.mk-cong λ where
  (s , inj₁ p) → ≈sym (swapᴵ (s , inj₁ p))
  (s , inj₂ n) → ≈sym (swapᴵ (s , inj₂ n)))

wire∘wire : (up : Pos B → Pos C) (down : Neg C → Neg B) (up′ : Pos A → Pos B) (down′ : Neg B → Neg A)
          → 𝒫._≈_ {A} {C} (𝒫._∘_ {A} {B} {C} (wireᴹ up down) (wireᴹ up′ down′))
              (wireᴹ (λ p → up (up′ p)) (λ n → down′ (down n)))
wire∘wire up down up′ down′ = wire-∘ᴹ up down (wireᴹ up′ down′) S.○ᴹ S.≲⇒≈ᴹ (S.mk-cong λ where
  (s , inj₁ p) → >>=ₚ-identityˡ (s , inj₂ (up′ p)) _
  (s , inj₂ n) → >>=ₚ-identityˡ (s , inj₁ (down′ (down n))) _)

sub-wire : (up : Pos X → Pos Y) (down : Neg Y → Neg X)
         → 𝒫._≈_ {X ⊗ᴵ A} {Y ⊗ᴵ A} (subᴵ {A = A} (wireᴹ up down)) (wireᴹ (Sum.map up (λ a → a)) (Sum.map down (λ a → a)))
sub-wire up down = S.≲⇒≈ᴹ (S.mk-cong λ where
  (s , inj₁ (inj₁ x)) → >>=ₚ-identityˡ (s , inj₂ (up x)) _
  (s , inj₁ (inj₂ a)) → ≈refl
  (s , inj₂ (inj₁ y)) → >>=ₚ-identityˡ (s , inj₁ (down y)) _
  (s , inj₂ (inj₂ a)) → ≈refl)

T₁-wire : (up : Pos A → Pos B) (down : Neg B → Neg A)
        → 𝒫._≈_ {Y ⊗ᴵ A} {Y ⊗ᴵ B} (T₁ᴵ Y (wireᴹ up down)) (wireᴹ (Sum.map (λ y → y) up) (Sum.map (λ y → y) down))
T₁-wire up down = S.≲⇒≈ᴹ (S.mk-cong λ where
  (s , inj₁ (inj₁ y)) → ≈refl
  (s , inj₁ (inj₂ a)) → >>=ₚ-identityˡ (s , inj₂ (up a)) _
  (s , inj₂ (inj₁ y)) → ≈refl
  (s , inj₂ (inj₂ b)) → >>=ₚ-identityˡ (s , inj₁ (down b)) _)
