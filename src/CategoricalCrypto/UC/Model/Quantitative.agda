{-# OPTIONS --safe --without-K --guardedness #-}

-- The model's quantitative UC setup: `UC.Quantitative.Observed` at the sealed
-- machine bundle (`docs/quantitative-uc-setup-plan.typ` §6).
--
-- The arguments are the ones `UC.Model.Observation` already gives `Induced`,
-- together with the approximation the observation was induced FROM — so
-- `_∼ᴼ_` IS closeness at every positive error, `induces` and `reflects` are
-- both the identity, and `UC.Model.Setup.ℰᵒ` is recovered as the `F₊` image of
-- the test presheaf.

open import ProbabilisticLogic.Dp.Advantage using (≈ₚ⇒≈ₚ[0])

open import CategoricalCrypto.Approx.Error using (ℚ-ordered)
open import CategoricalCrypto.UC.Approximate using (ApproximateObservation)
open import CategoricalCrypto.UC.Machine using (Approximationᴹ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Observation
  using (approximateᵒ; obs-resp; observationᵒ; Obs; Ωᵒ; 𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (∣𝔾ᵒ∣; 𝔾ᵒ)
open import CategoricalCrypto.UC.Quantitative.Query using (fromBudget; module Tests)

module CategoricalCrypto.UC.Model.Quantitative where

private module Aᵒ = ApproximateObservation approximateᵒ

open import CategoricalCrypto.UC.Quantitative.Observed
  𝔾ᵒ ℚ-ordered observationᵒ Aᵒ.approx Aᵒ.⟦⟧-resp-≈₀ public
  renaming (Q to Qᵒ; QSetup to QSetupᵒ; module Quant to QUCᵒ)

open Absorbing (λ h → h) public
open Reflecting (λ h → h) public

-- The same observation restricted by allowance: `UC.Quantitative.Query` at
-- this branch's budget.  It is a DIFFERENT space from `spaceᵗ` above, which
-- admits every closure at one scalar error.
module Queryᵒ = Tests ∣𝔾ᵒ∣ (fromBudget budgetᵒ) Approximationᴹ 𝟘ᵒ Ωᵒ Obs
                     (λ e → ≈ₚ⇒≈ₚ[0] (obs-resp e))
