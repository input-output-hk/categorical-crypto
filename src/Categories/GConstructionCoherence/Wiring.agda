{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The three solver-discharged obligations of the segment decomposition
-- (one generator box each; the 50-morphism coherence equation is never
-- solved whole):
--
--   ob₀ : ρ₁ ∘ R₀ ≈ L₀          ob₁ : ρ₂ ∘ R₁ ≈ L₁ ∘ ρ₁
--   ob₂ : R₂ ≈ L₂ ∘ ρ₂
--
-- Chaining them (pure congruence) gives R₂∘R₁∘R₀ ≈ L₂∘L₁∘L₀ with no
-- residual ρ-cancellation:
--   R₂∘R₁∘R₀ ≈ (L₂∘ρ₂)∘R₁∘R₀ ≈ L₂∘(L₁∘ρ₁)∘R₀ ≈ L₂∘L₁∘L₀.
--------------------------------------------------------------------------------

-- STATUS (2026-06-10): DESIGN COMPLETE, TYPE-VALIDATED; OBLIGATION EVALUATION
-- EXCEEDS INTERACTIVE COMPUTE.  Terms.agda (all segment interfaces + routing
-- isos) typechecks.  The solver obligations in Wiring0/1/2 are well-typed but
-- each forces a findIsoᵀ evaluation whose per-call cost at this 8-atom
-- signature is dominated by raw-⟪⟫ type-conversion overhead (ob₂, the
-- SMALLEST: >20 min, timed out).  Residual options: (a) batch/overnight
-- compute, (b) hand-prove the three 1-box naturality squares with free
-- combinators (~150-400 LOC, no solver), (c) eliminate the per-call
-- type-conversion overhead.  See docs/smc-solver-performance.md.
module Categories.GConstructionCoherence.Wiring where

open import Categories.GConstructionCoherence.Terms
open import Categories.GConstructionCoherence.Wiring0 public using (ob₀)
open import Categories.GConstructionCoherence.Wiring1 public using (ob₁)
open import Categories.GConstructionCoherence.Wiring2 public using (ob₂)

-- The assembled segment-level equality.
segments : (R₂ᵗ ∘ R₁ᵗ ∘ R₀ᵗ) ≈Term (L₂ᵗ ∘ L₁ᵗ ∘ L₀ᵗ)
segments =
  ≈-Term-trans (∘-resp-≈ ob₂ ≈-Term-refl)                    -- (L₂∘ρ₂)∘(R₁∘R₀)
  (≈-Term-trans assoc                                         -- L₂∘(ρ₂∘(R₁∘R₀))
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))     -- L₂∘((ρ₂∘R₁)∘R₀)
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl (∘-resp-≈ ob₁ ≈-Term-refl))  -- L₂∘((L₁∘ρ₁)∘R₀)
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)                  -- L₂∘(L₁∘(ρ₁∘R₀))
               (∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl ob₀))))))  -- L₂∘(L₁∘L₀)
