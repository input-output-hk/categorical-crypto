{-# OPTIONS --safe --without-K #-}

-- SPIKE: the category of Mealy machines over a symmetric monoidal `𝒱`.
--
-- `Spike.Interchange` supplies the three interchange identities; everything
-- here is bookkeeping on top of them.  The crux is `run-∘`: unrolling a
-- composite `n` steps is the same as composing the two unrollings, which is
-- `CategoricalCrypto.SFunM`'s `trace-∘` written point-free.

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; zero; suc; [_]; [_,_]; _∷_; [])

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Data.Nat.Base using (ℕ; zero; suc)

import CategoricalCrypto.SFunM.Spike.Interchange as Interchange
import CategoricalCrypto.SFunM.Spike.Mealy as Mealy

module CategoricalCrypto.SFunM.Spike.Laws {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided using (σ⇒)
open MonoidalUtilities.Shorthands monoidal
open Mealy 𝒱
open Interchange 𝒱

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A A′ B B′ C C′ P Q : Obj

------------------------------------------------------------------------
-- The composite step
------------------------------------------------------------------------

-- `Machine.step (g ∘ᴹ f)` is `compK (step g) (step f)`.
compK : (P ⊗₀ B ⇒ P ⊗₀ C) → (Q ⊗₀ A ⇒ Q ⊗₀ B) → (P ⊗₀ Q) ⊗₀ A ⇒ (P ⊗₀ Q) ⊗₀ C
compK g f = onL g ∘ onR f

onL-id : onL {Q = Q} (id {P ⊗₀ A}) ≈ id
onL-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ swp-swp

onR-id : onR {P = P} (id {Q ⊗₀ A}) ≈ id
onR-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ associator.isoˡ

compK-id : compK (id {P ⊗₀ A}) (id {Q ⊗₀ A}) ≈ id
compK-id = (onL-id ⟩∘⟨ onR-id) ○ identity²

------------------------------------------------------------------------
-- The two state factors act on complementary interface slots
------------------------------------------------------------------------

-- Both sides are the `Ω`-conjugate of `g ⊗₁ f`; only the order in which the
-- two disjoint boxes fire differs.
slot-comm : {g : P ⊗₀ B ⇒ P ⊗₀ C} {f : Q ⊗₀ A′ ⇒ Q ⊗₀ B′}
          → slot₂ {Z = C} (onR {P = P} f) ∘ slot₁ {Z = A′} (onL {Q = Q} g)
          ≈ slot₁ {Z = B′} (onL {Q = Q} g) ∘ slot₂ {Z = B} (onR {P = P} f)
slot-comm {P = P} {B} {C} {Q} {A′} {B′} {g} {f} = begin
  slot₂ (onR f) ∘ slot₁ (onL g)
    ≈⟨ Gᶠ.slot₂-onR-Ω ⟩∘⟨ Gᵍ.slot₁-onL ⟩
  (Ω ∘ (id ⊗₁ f ∘ Ω)) ∘ (Ω ∘ (g ⊗₁ id ∘ Ω))
    ≈⟨ center (cancelʳ Ω-involutive) ⟩
  Ω ∘ (id ⊗₁ f ∘ (g ⊗₁ id ∘ Ω))
    ≈⟨ refl⟩∘⟨ pullˡ (⟺ serialize₂₁ ○ serialize₁₂) ⟩
  Ω ∘ ((g ⊗₁ id ∘ id ⊗₁ f) ∘ Ω)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  Ω ∘ (g ⊗₁ id ∘ (id ⊗₁ f ∘ Ω))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ insertˡ Ω-involutive ⟩
  Ω ∘ (g ⊗₁ id ∘ (Ω ∘ (Ω ∘ (id ⊗₁ f ∘ Ω))))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  Ω ∘ ((g ⊗₁ id ∘ Ω) ∘ (Ω ∘ (id ⊗₁ f ∘ Ω)))
    ≈⟨ sym-assoc ⟩
  (Ω ∘ (g ⊗₁ id ∘ Ω)) ∘ (Ω ∘ (id ⊗₁ f ∘ Ω))
    ≈˘⟨ Gᵍ′.slot₁-onL ⟩∘⟨ Gᶠ′.slot₂-onR-Ω ⟩
  slot₁ (onL g) ∘ slot₂ (onR f)  ∎
  where
    module Gᵍ  = OneGen  P Q B C A′ g
    module Gᵍ′ = OneGen  P Q B C B′ g
    module Gᶠ  = OneGenʳ P Q A′ B′ C f
    module Gᶠ′ = OneGenʳ P Q A′ B′ B f

-- Slotting a composite step: this is the whole content of `run-∘`.
compK-slot : {g₁ : P ⊗₀ B ⇒ P ⊗₀ C} {f₁ : Q ⊗₀ A ⇒ Q ⊗₀ B}
             {g₂ : P ⊗₀ B′ ⇒ P ⊗₀ C′} {f₂ : Q ⊗₀ A′ ⇒ Q ⊗₀ B′}
           → slot₂ {Z = C} (compK g₂ f₂) ∘ slot₁ {Z = A′} (compK g₁ f₁)
           ≈ compK (slot₂ g₂ ∘ slot₁ g₁) (slot₂ f₂ ∘ slot₁ f₁)
compK-slot {P = P} {B} {C} {Q} {A} {B′} {C′} {A′} {g₁} {f₁} {g₂} {f₂} = begin
  slot₂ (onL g₂ ∘ onR f₂) ∘ slot₁ (onL g₁ ∘ onR f₁)
    ≈⟨ slot₂ᵍ-∘ ⟩∘⟨ slot₁ᵍ-∘ ⟩
  (slot₂ (onL g₂) ∘ slot₂ (onR f₂)) ∘ (slot₁ (onL g₁) ∘ slot₁ (onR f₁))
    ≈⟨ assoc ⟩
  slot₂ (onL g₂) ∘ (slot₂ (onR f₂) ∘ (slot₁ (onL g₁) ∘ slot₁ (onR f₁)))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  slot₂ (onL g₂) ∘ ((slot₂ (onR f₂) ∘ slot₁ (onL g₁)) ∘ slot₁ (onR f₁))
    ≈⟨ refl⟩∘⟨ slot-comm ⟩∘⟨refl ⟩
  slot₂ (onL g₂) ∘ ((slot₁ (onL g₁) ∘ slot₂ (onR f₂)) ∘ slot₁ (onR f₁))
    ≈⟨ refl⟩∘⟨ assoc ⟩
  slot₂ (onL g₂) ∘ (slot₁ (onL g₁) ∘ (slot₂ (onR f₂) ∘ slot₁ (onR f₁)))
    ≈⟨ sym-assoc ⟩
  (slot₂ (onL g₂) ∘ slot₁ (onL g₁)) ∘ (slot₂ (onR f₂) ∘ slot₁ (onR f₁))
    ≈⟨ (Hᵍ.slot₂-onL-comm ⟩∘⟨ Hᵍ′.slot₁-onL-comm) ⟩∘⟨ (Hᶠ.slot₂-onR ⟩∘⟨ Hᶠ′.slot₁-onR) ⟩
  (onL (slot₂ g₂) ∘ onL (slot₁ g₁)) ∘ (onR (slot₂ f₂) ∘ onR (slot₁ f₁))
    ≈˘⟨ onL-∘ ⟩∘⟨ onRᵍ-∘ ⟩
  onL (slot₂ g₂ ∘ slot₁ g₁) ∘ onR (slot₂ f₂ ∘ slot₁ f₁)  ∎
  where
    module Hᵍ  = OneGen  P Q B′ C′ C g₂
    module Hᵍ′ = OneGen  P Q B  C  B′ g₁
    module Hᶠ  = OneGenʳ P Q A′ B′ B f₂
    module Hᶠ′ = OneGenʳ P Q A  B  A′ f₁

------------------------------------------------------------------------
-- Unrolling
------------------------------------------------------------------------

slot₁-id : ∀ {X Z} → slot₁ {P} {X} {X} {Z} id ≈ id
slot₁-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ associator.isoʳ

slot₂-id : ∀ {X Z} → slot₂ {P} {X} {X} {Z} id ≈ id
slot₂-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ untuck-tuck

-- The point-free `trace-∘`: pairing states commutes with pairing interfaces.
run-∘ : (g : Machine B C) (f : Machine A B) (n : ℕ)
      → run (g ∘ᴹ f) n ≈ compK (run g n) (run f n)
run-∘ g f zero    = ⟺ compK-id
run-∘ g f (suc n) = (slot₂ᵍ-cong (run-∘ g f n) ⟩∘⟨refl) ○ compK-slot

run-id : (n : ℕ) → run (idᴹ {A}) n ≈ id
run-id zero    = Equiv.refl
run-id (suc n) = (slot₂ᵍ-cong (run-id n) ⟩∘⟨ slot₁-id) ○ identityʳ ○ slot₂-id

eval-id : (n : ℕ) → eval (idᴹ {A}) n ≈ id
eval-id n = begin
  λ⇒ ∘ (id ⊗₁ id ∘ (run idᴹ n ∘ (id ⊗₁ id ∘ λ⇐)))
    ≈⟨ refl⟩∘⟨ elimˡ ⊗.identity ⟩
  λ⇒ ∘ (run idᴹ n ∘ (id ⊗₁ id ∘ λ⇐))
    ≈⟨ refl⟩∘⟨ run-id n ⟩∘⟨refl ⟩
  λ⇒ ∘ (id ∘ (id ⊗₁ id ∘ λ⇐))
    ≈⟨ refl⟩∘⟨ identityˡ ⟩
  λ⇒ ∘ (id ⊗₁ id ∘ λ⇐)
    ≈⟨ refl⟩∘⟨ elimˡ ⊗.identity ⟩
  λ⇒ ∘ λ⇐
    ≈⟨ unitorˡ.isoʳ ⟩
  id  ∎
