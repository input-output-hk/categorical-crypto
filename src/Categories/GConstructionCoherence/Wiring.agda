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
-- "the 8-atom wall" + follow-ups):
--   * forcing routed through refl-checked equations (`solve!`/`stepR!` from
--     `Terms`), never `from-just`/inferred witnesses (slow elaborator path);
--   * the gate itself lives in `Split`, where `⟪_⟫` and `soundness` are
--     instantiated from the SAME `sig` and so spell the translation
--     identically (syntactic fast path in conversion);
--   * one module for all three obligations (a merge with `Decomp` would be
--     perf-neutral — measured 0.5 % — since `Split` already gives both the
--     same import cone; the boundary is narrative, not a cost);
--   * plain `findIso` (~20% cheaper than `findIsoᵀ` on 1-box cross-pairs);
--   * the solver sees BALANCED ∘-spellings of the obligation sides
--     (α/γ internals included) — measured 6.4×/1.7× cheaper than the
--     right-linear segment forms — bridged back to the segment statements
--     by near-free pure-assoc `solveSplitR?` conversions.
--------------------------------------------------------------------------------

module Categories.GConstructionCoherence.Wiring where

open import Relation.Binary.PropositionalEquality using (refl)
open import Categories.FreeMonoidal using (Symm; _≤_; v≤v)
open import Categories.GConstructionCoherence.Terms
open import Categories.Category using (Category)
open import Categories.Morphism.Reasoning FreeMonoidal using (center; pullʳ)
open Category.HomReasoning FreeMonoidal using (_○_; _⟩∘⟨refl; refl⟩∘⟨_)

private instance S≤S : Symm ≤ Symm
                 S≤S = v≤v

private
  -- balanced clones of the routing isos (same morphisms, balanced ∘-trees)
  βᵇ : ∀ {P Q R} → HomTerm ((P ⊗₀ Q) ⊗₀ R) ((P ⊗₀ R) ⊗₀ Q)
  βᵇ = (α⇐ ∘ id ⊗₁ σ) ∘ α⇒

  αᵇ : ∀ {A⁻' B⁺' B⁻' C⁺'}
     → HomTerm ((B⁻' ⊗₀ C⁺') ⊗₀ (A⁻' ⊗₀ B⁺')) ((A⁻' ⊗₀ C⁺') ⊗₀ (B⁻' ⊗₀ B⁺'))
  αᵇ = ((α⇒ ∘ σ ⊗₁ id) ∘ (α⇐ ∘ id ⊗₁ (σ ⊗₁ id))) ∘ (id ⊗₁ α⇐ ∘ α⇒)

  γᵇ : ∀ {A⁺' B⁺' B⁻' C⁻'}
     → HomTerm ((A⁺' ⊗₀ C⁻') ⊗₀ (B⁻' ⊗₀ B⁺')) ((B⁺' ⊗₀ C⁻') ⊗₀ (A⁺' ⊗₀ B⁻'))
  γᵇ = ((α⇒ ∘ σ ⊗₁ id) ∘ (α⇐ ∘ id ⊗₁ (σ ⊗₁ id))) ∘ ((id ⊗₁ α⇐ ∘ α⇒) ∘ id ⊗₁ σ)

  -- balanced spellings of the six obligation sides
  ρ₁R₀ᵇ L₀ᵇ : HomTerm (((A⁺ ⊗₀ E⁻) ⊗₀ (D⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺))
                      (((B⁺ ⊗₀ E⁻) ⊗₀ (A⁻ ⊗₀ B⁺)) ⊗₀ (D⁻ ⊗₀ D⁺))
  ρ₁R₀ᵇ = ((βᵇ ∘ (id ⊗₁ σ ∘ σ ∘ αᵇ) ⊗₁ id) ∘ (βᵇ ∘ σ))
        ∘ ((id ⊗₁ (id ⊗₁ f') ∘ id ⊗₁ γᵇ) ∘ (α⇒ ∘ γᵇ ⊗₁ id))
  L₀ᵇ = ((id ⊗₁ f') ⊗₁ id ∘ γᵇ ⊗₁ id) ∘ βᵇ

  ρ₂R₁ᵇ L₁ρ₁ᵇ : HomTerm ((D⁺ ⊗₀ E⁻) ⊗₀ ((B⁺ ⊗₀ D⁻) ⊗₀ (A⁻ ⊗₀ B⁺)))
                        (((D⁺ ⊗₀ E⁻) ⊗₀ (B⁻ ⊗₀ D⁺)) ⊗₀ (A⁻ ⊗₀ B⁺))
  ρ₂R₁ᵇ = α⇐ ∘ id ⊗₁ (g' ⊗₁ id)
  L₁ρ₁ᵇ = (((id ⊗₁ g') ⊗₁ id ∘ γᵇ ⊗₁ id) ∘ (βᵇ ∘ βᵇ))
        ∘ (((id ⊗₁ σ ∘ σ) ∘ αᵇ) ⊗₁ id ∘ (βᵇ ∘ σ))

  R₂ᵇ L₂ρ₂ᵇ : HomTerm ((D⁺ ⊗₀ E⁻) ⊗₀ ((B⁻ ⊗₀ D⁺) ⊗₀ (A⁻ ⊗₀ B⁺)))
                      (((A⁻ ⊗₀ E⁺) ⊗₀ (D⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺))
  R₂ᵇ = (αᵇ ⊗₁ id ∘ (h' ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ id ⊗₁ αᵇ)
  L₂ρ₂ᵇ = ((βᵇ ∘ αᵇ ⊗₁ id) ∘ (βᵇ ∘ αᵇ ⊗₁ id)) ∘ ((h' ⊗₁ id) ⊗₁ id ∘ α⇐)


-- the obligations at the segment statements: pure-assoc bridges around the
-- solver obligation on the balanced spellings
ob₀ : (ρ₁ᵗ ∘ R₀ᵗ) ≈Term L₀ᵗ
ob₀ = stepR! (ρ₁ᵗ ∘ R₀ᵗ) ρ₁R₀ᵇ refl ○ solve! ρ₁R₀ᵇ L₀ᵇ refl ○ stepR! L₀ᵇ L₀ᵗ refl

ob₁ : (ρ₂ᵗ ∘ R₁ᵗ) ≈Term (L₁ᵗ ∘ ρ₁ᵗ)
ob₁ = stepR! (ρ₂ᵗ ∘ R₁ᵗ) ρ₂R₁ᵇ refl ○ solve! ρ₂R₁ᵇ L₁ρ₁ᵇ refl ○ stepR! L₁ρ₁ᵇ (L₁ᵗ ∘ ρ₁ᵗ) refl

ob₂ : R₂ᵗ ≈Term (L₂ᵗ ∘ ρ₂ᵗ)
ob₂ = stepR! R₂ᵗ R₂ᵇ refl ○ solve! R₂ᵇ L₂ρ₂ᵇ refl ○ stepR! L₂ρ₂ᵇ (L₂ᵗ ∘ ρ₂ᵗ) refl

-- The assembled segment-level equality: the standard three-square paste.
segments : (R₂ᵗ ∘ R₁ᵗ ∘ R₀ᵗ) ≈Term (L₂ᵗ ∘ L₁ᵗ ∘ L₀ᵗ)
segments = ob₂ ⟩∘⟨refl ○ center ob₁ ○ (refl⟩∘⟨ pullʳ ob₀)
