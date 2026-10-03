{-# OPTIONS --safe --without-K --guardedness #-}

-- `UCSetup` at the machine FAMILY: `UC.Family` instantiated at the
-- sealed bundle, so the inherited metatheory is available asymptotically in
-- the negligible tier (`Canonicalᴺ`);
-- `UC.Quantitative.Family` gives the quantitative contextual relation
-- `_≈ctx[_]_` and the simulator-bearing emulation witness `_≤UC^ωᵉ_` over it.

open import Data.Nat.Base

open import ProbabilisticLogic.Distribution.Uniform.Decay

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal

module CategoricalCrypto.UC.Model.Family where

open import CategoricalCrypto.UC.Family
  𝔾ᵒ qevaluationᵒ gradingᵒ ℕ (λ n → n) public

open import CategoricalCrypto.UC.Quantitative.Family 𝔾ᵒ gradingᵒ qevaluationᵒ public

-- An interface family as an object family of the seal.
ifaceᶠ : (ℕ → Iface) → Obj^ω
ifaceᶠ B n = ifaceᵒ (B n)
