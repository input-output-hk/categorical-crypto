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

-- STATUS (2026-06-10): COMPLETE.  The whole chain typechecks in ~2.5 min
-- (obligations ~30 s each) after fixing two call-pattern performance bugs —
-- see docs/smc-solver-performance.md ("the 8-atom wall: RESOLVED"):
--   * forcing must be routed through refl-checked equations (`force!`),
--     never `from-just`/inferred witnesses (slow elaborator path);
--   * instantiated types must be SPELLED as the consuming signature spells
--     them (Translation (APROPSignatureDec.sig gSigDec), not Translation gSig).
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
