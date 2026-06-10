{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The three solver-discharged obligations of the segment decomposition
-- (one generator box each; the 50-morphism coherence equation is never
-- solved whole):
--
--   ob₀ : ρ₁ ∘ R₀ ≈ L₀          ob₁ : ρ₂ ∘ R₁ ≈ L₁ ∘ ρ₁
--   ob₂ : R₂ ≈ L₂ ∘ ρ₂
--
-- chained by pure congruence into `segments` (no ρ-cancellation needed).
--
-- Performance-critical call pattern (docs/smc-solver-performance.md,
-- "the 8-atom wall"):
--   * forcing is routed through refl-checked equations (`force!`), never
--     `from-just`/inferred witnesses (slow elaborator path);
--   * ⟪_⟫ is spelled EXACTLY as SoundnessFullWired's instantiated signature
--     spells it (syntactic fast path in conversion);
--   * one module for all three obligations (the ~15 s import overhead is
--     paid once);
--   * plain `findIso` (measured ~20% cheaper than `findIsoᵀ` on these
--     1-box cross-pairs).
--------------------------------------------------------------------------------

module Categories.GConstructionCoherence.Wiring where

open import Data.Bool.Base using (true)
open import Data.Maybe.Base using (Maybe; just; is-just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Categories.GConstructionCoherence.Terms
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)
open import Categories.APROP.Hypergraph.Translation (APROPSignatureDec.sig gSigDec) using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.FindIso gSigDec using (findIso)
open import Categories.APROP.Hypergraph.SoundnessFullWired gSigDec
  using (soundness-full-wired)

private
  force! : ∀ {a} {A : Set a} (m : Maybe A) → is-just m ≡ true → A
  force! (just x) _ = x

  iso₀ : ⟪ ρ₁ᵗ ∘ R₀ᵗ ⟫ ≅ᴴ ⟪ L₀ᵗ ⟫
  iso₀ = force! (findIso ⟪ ρ₁ᵗ ∘ R₀ᵗ ⟫ ⟪ L₀ᵗ ⟫) refl

  iso₁ : ⟪ ρ₂ᵗ ∘ R₁ᵗ ⟫ ≅ᴴ ⟪ L₁ᵗ ∘ ρ₁ᵗ ⟫
  iso₁ = force! (findIso ⟪ ρ₂ᵗ ∘ R₁ᵗ ⟫ ⟪ L₁ᵗ ∘ ρ₁ᵗ ⟫) refl

  iso₂ : ⟪ R₂ᵗ ⟫ ≅ᴴ ⟪ L₂ᵗ ∘ ρ₂ᵗ ⟫
  iso₂ = force! (findIso ⟪ R₂ᵗ ⟫ ⟪ L₂ᵗ ∘ ρ₂ᵗ ⟫) refl

ob₀ : (ρ₁ᵗ ∘ R₀ᵗ) ≈Term L₀ᵗ
ob₀ = soundness-full-wired {f = ρ₁ᵗ ∘ R₀ᵗ} {g = L₀ᵗ} iso₀

ob₁ : (ρ₂ᵗ ∘ R₁ᵗ) ≈Term (L₁ᵗ ∘ ρ₁ᵗ)
ob₁ = soundness-full-wired {f = ρ₂ᵗ ∘ R₁ᵗ} {g = L₁ᵗ ∘ ρ₁ᵗ} iso₁

ob₂ : R₂ᵗ ≈Term (L₂ᵗ ∘ ρ₂ᵗ)
ob₂ = soundness-full-wired {f = R₂ᵗ} {g = L₂ᵗ ∘ ρ₂ᵗ} iso₂

-- The assembled segment-level equality.
segments : (R₂ᵗ ∘ R₁ᵗ ∘ R₀ᵗ) ≈Term (L₂ᵗ ∘ L₁ᵗ ∘ L₀ᵗ)
segments =
  ≈-Term-trans (∘-resp-≈ ob₂ ≈-Term-refl)
  (≈-Term-trans assoc
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl (∘-resp-≈ ob₁ ≈-Term-refl))
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)
               (∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl ob₀))))))
