{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Quantitative.Family` at the sealed machine bundle: the quantitative
-- contextual relation `_≈ctx[_]_` on families of graded morphisms, and the
-- simulator-bearing emulation witness `_≤UC^ωᵉ_` over it.

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered

open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal

module CategoricalCrypto.UC.Model.Family.Contextual where

private module P = AllPositive ℚ-refinement (QEvaluation.approx qevaluationᵒ)

-- Spelled exactly as `Approx.Evaluation.qual₊` spells it, so that the readout
-- this module lands at IS `evaluationᵒ`, the two orders are the same one, and
-- the `reflects` input is the identity.
open import CategoricalCrypto.UC.Quantitative.Family
  𝔾ᵒ qevaluationᵒ gradingᵒ
  P.∼ᵃ-isEquivalence P.zero⇒positive (λ h → h) public
