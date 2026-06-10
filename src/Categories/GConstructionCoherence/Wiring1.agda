{-# OPTIONS --safe --without-K #-}
-- Segment obligation ob1 (see Wiring.agda).  Performance-critical call
-- pattern (docs/smc-solver-performance.md, "the 8-atom wall"):
--   * forcing is routed through a refl-checked equation (force!), never
--     from-just / inferred witnesses (slow elaborator path);
--   * ⟪_⟫ is spelled EXACTLY as SoundnessFullWired's instantiated signature
--     spells it, so type conversion hits the syntactic fast path.
module Categories.GConstructionCoherence.Wiring1 where

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
  iso₁ : ⟪ ρ₂ᵗ ∘ R₁ᵗ ⟫ ≅ᴴ ⟪ L₁ᵗ ∘ ρ₁ᵗ ⟫
  iso₁ = force! (findIsoᵀ ⟪ ρ₂ᵗ ∘ R₁ᵗ ⟫ ⟪ L₁ᵗ ∘ ρ₁ᵗ ⟫) refl

ob₁ : (ρ₂ᵗ ∘ R₁ᵗ) ≈Term (L₁ᵗ ∘ ρ₁ᵗ)
ob₁ = soundness-full-wired {f = ρ₂ᵗ ∘ R₁ᵗ} {g = L₁ᵗ ∘ ρ₁ᵗ} iso₁
