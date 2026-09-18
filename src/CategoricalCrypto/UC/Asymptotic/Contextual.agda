{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Quantitative.Family` at the sealed machine bundle: the quantitative
-- contextual relation `_≈ctx[_]_` on families of graded morphisms, and the
-- simulator-bearing emulation witness `_≤UC^ωᵉ_` over it.
--
-- The two model-specific inputs are `UC.Model.Observation`'s: its `obs-resp`
-- sees the seal's hom equality EXACTLY, which is the zero-error input the
-- generic module asks for, and its `_∼_` IS closeness at every positive error
-- (`UC.Approximate.Induced`), so the `reflects` input is the identity.

open import ProbabilisticLogic.Dp.Advantage using (≈ₚ⇒≈ₚ[0])

open import CategoricalCrypto.UC.Machine using (Approximationᴹ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Observation using (obs-resp; observationᵒ)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ)

module CategoricalCrypto.UC.Asymptotic.Contextual where

open import CategoricalCrypto.UC.Quantitative.Family
  𝔾ᵒ observationᵒ budgetᵒ Approximationᴹ (λ h → h)
  (λ e → ≈ₚ⇒≈ₚ[0] (obs-resp e)) public
