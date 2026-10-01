{-# OPTIONS --safe --without-K --guardedness #-}

-- The model's quantitative UC setup: `UC.Quantitative.Observed` at the sealed
-- machine bundle (`docs/quantitative-uc-setup-plan.typ` §6), at which
-- `UC.Model.Setup.ℰᵒ` is recovered as the `F₊` image of the test presheaf.

open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Quantitative.Query

module CategoricalCrypto.UC.Model.Quantitative where

private module P = AllPositive ℚ-refinement (QEvaluation.approx qevaluationᵒ)

-- Spelled as `Approx.Evaluation.qual₊` spells it: see `UC.Model.Family.Contextual`.
open import CategoricalCrypto.UC.Quantitative.Observed
  𝔾ᵒ ℚ-ordered qevaluationᵒ
  P.∼ᵃ-isEquivalence P.zero⇒positive
  public renaming (Q to Qᵒ; QSetup to QSetupᵒ; module Quant to QUCᵒ; module AllPositive to AllPositiveᵒ)

open AllPositiveᵒ ℚ-refinement public
open Absorbing (λ h → h) public
open Reflecting (λ h → h) public

-- The same observation restricted by allowance: `UC.Quantitative.Query` at
-- the model's grading.  It is a DIFFERENT space from `spaceᵗ` above, which
-- admits every closure at one scalar error.
module Queryᵒ = Tests 𝔾ᵒ gradingᵒ Approximationᴹ 𝟘ᵒ Ωᵒ Obs (λ e → ≈ₚ⇒≈ₚ[0] (obs-resp e))
