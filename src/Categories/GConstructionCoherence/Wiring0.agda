{-# OPTIONS --safe --without-K #-}
-- Segment obligation ob0 (see Wiring.agda).  Performance-critical call
-- pattern (docs/smc-solver-performance.md, "the 8-atom wall"):
--   * forcing is routed through a refl-checked equation (force!), never
--     from-just / inferred witnesses (slow elaborator path);
--   * ⟪_⟫ is spelled EXACTLY as SoundnessFullWired's instantiated signature
--     spells it, so type conversion hits the syntactic fast path.
module Categories.GConstructionCoherence.Wiring0 where

open import Data.Bool.Base using (true)
open import Data.Maybe.Base using (Maybe; just; is-just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Categories.GConstructionCoherence.Terms
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)
open import Categories.APROP.Hypergraph.Translation (APROPSignatureDec.sig gSigDec) using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.FindIsoTab gSigDec using (findIsoᵀ)
open import Categories.APROP.Hypergraph.SoundnessFullWired gSigDec
  using (soundness-full-wired)

private
  force! : ∀ {a} {A : Set a} (m : Maybe A) → is-just m ≡ true → A
  force! (just x) _ = x

private
  iso₀ : ⟪ ρ₁ᵗ ∘ R₀ᵗ ⟫ ≅ᴴ ⟪ L₀ᵗ ⟫
  iso₀ = force! (findIsoᵀ ⟪ ρ₁ᵗ ∘ R₀ᵗ ⟫ ⟪ L₀ᵗ ⟫) refl

ob₀ : (ρ₁ᵗ ∘ R₀ᵗ) ≈Term L₀ᵗ
ob₀ = soundness-full-wired {f = ρ₁ᵗ ∘ R₀ᵗ} {g = L₀ᵗ} iso₀
