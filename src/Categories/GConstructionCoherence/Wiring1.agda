{-# OPTIONS --safe --without-K #-}
-- STATUS (2026-06-10): DESIGN COMPLETE, TYPE-VALIDATED; OBLIGATION EVALUATION
-- EXCEEDS INTERACTIVE COMPUTE.  Terms.agda (all segment interfaces + routing
-- isos) typechecks.  The solver obligations in Wiring0/1/2 are well-typed but
-- each forces a findIsoᵀ evaluation whose per-call cost at this 8-atom
-- signature is dominated by raw-⟪⟫ type-conversion overhead (ob₂, the
-- SMALLEST: >20 min, timed out).  Residual options: (a) batch/overnight
-- compute, (b) hand-prove the three 1-box naturality squares with free
-- combinators (~150-400 LOC, no solver), (c) eliminate the per-call
-- type-conversion overhead.  See docs/smc-solver-performance.md.
module Categories.GConstructionCoherence.Wiring1 where

open import Data.Maybe.Base using (from-just)
open import Categories.GConstructionCoherence.Terms
open import Categories.APROP.Hypergraph.Translation gSig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.FindIsoTab gSigDec using (findIsoᵀ)
open import Categories.APROP.Hypergraph.SoundnessFullWired gSigDec
  using (soundness-full-wired)

ob₁ : (ρ₂ᵗ ∘ R₁ᵗ) ≈Term (L₁ᵗ ∘ ρ₁ᵗ)
ob₁ = soundness-full-wired
        (from-just (findIsoᵀ ⟪ ρ₂ᵗ ∘ R₁ᵗ ⟫ ⟪ L₁ᵗ ∘ ρ₁ᵗ ⟫))
