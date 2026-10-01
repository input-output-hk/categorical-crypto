{-# OPTIONS --safe --without-K --guardedness #-}

-- `UCSetup` at the machine FAMILY: `UC.Family` instantiated at the
-- sealed bundle, so the inherited metatheory is available asymptotically, with
-- `UC.Family.Vanishing` on the same ingredients supplying `Canonical^ω`, the
-- INHERITED order, where `UC-compose` is, and `UC.Family.Negligible{,.Setup}`
-- the negligible tier's readout and emulation order.

open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product.Base

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal

module CategoricalCrypto.UC.Model.Family where

open import CategoricalCrypto.UC.Family
  𝔾ᵒ qevaluationᵒ gradingᵒ ℕ (λ n → n) (λ N → N , ≤-refl) public

open import CategoricalCrypto.UC.Family.Vanishing
  𝔾ᵒ qevaluationᵒ gradingᵒ ℕ (λ n → n) (λ N → N , ≤-refl) public

open import CategoricalCrypto.UC.Family.Negligible
  𝔾ᵒ qevaluationᵒ gradingᵒ ℕ (λ n → n) (λ N → N , ≤-refl) public

open import CategoricalCrypto.UC.Family.Negligible.Setup
  𝔾ᵒ qevaluationᵒ gradingᵒ ℕ (λ n → n) (λ N → N , ≤-refl) public

-- An interface family as an object family of the seal.
ifaceᶠ : (ℕ → Iface) → Obj^ω
ifaceᶠ B n = ifaceᵒ (B n)
