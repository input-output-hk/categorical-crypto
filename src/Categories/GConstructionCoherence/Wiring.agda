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
--   * forcing routed through refl-checked equations (`force!`), never
--     `from-just`/inferred witnesses (slow elaborator path);
--   * ⟪_⟫ spelled EXACTLY as Soundness's instantiated signature
--     spells it (syntactic fast path in conversion);
--   * one module for all three obligations (~15 s import overhead once);
--   * plain `findIso` (~20% cheaper than `findIsoᵀ` on 1-box cross-pairs);
--   * the solver sees BALANCED ∘-spellings of the obligation sides
--     (α/γ internals included) — measured 6.4×/1.7× cheaper than the
--     right-linear segment forms — bridged back to the segment statements
--     by near-free pure-assoc `solveSplitR?` conversions.
--------------------------------------------------------------------------------

module Categories.GConstructionCoherence.Wiring where

open import Data.Bool.Base using (true)
open import Data.Maybe.Base using (Maybe; just; is-just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Categories.FreeMonoidal using (Symm; _≤_; v≤v)
open import Categories.GConstructionCoherence.Terms
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)
open import Categories.APROP.Hypergraph.Model.Translation (APROPSignatureDec.sig gSigDec) using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.Match.FindIso gSigDec using (findIso)
open import Categories.APROP.Hypergraph.Solver.Split gSigDec using (solveSplitR?)
open import Categories.APROP.Hypergraph.Soundness gSigDec
  using (soundness)

private instance S≤S : Symm ≤ Symm
                 S≤S = v≤v

private
  force! : ∀ {a} {A : Set a} (m : Maybe A) → is-just m ≡ true → A
  force! (just x) _ = x

  -- pure-assoc respelling, validated by reassoc+refl (no solver leaf)
  assoc! : ∀ {A B} (f g : HomTerm A B) → is-just (solveSplitR? f g) ≡ true → f ≈Term g
  assoc! f g ok = force! (solveSplitR? f g) ok

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

  -- one leaf, one line: the search's success is discharged by a refl-checked
  -- equation, never by an inferred witness (the `Decomp.step!` idiom)
  solve! : ∀ {A B} (f g : HomTerm A B)
         → is-just (findIso ⟪ f ⟫ ⟪ g ⟫) ≡ true → f ≈Term g
  solve! f g ok = soundness {f = f} {g = g} (force! (findIso ⟪ f ⟫ ⟪ g ⟫) ok)

  -- the solver obligations, on the balanced spellings
  ob₀ᵇ : ρ₁R₀ᵇ ≈Term L₀ᵇ
  ob₀ᵇ = solve! ρ₁R₀ᵇ L₀ᵇ refl

  ob₁ᵇ : ρ₂R₁ᵇ ≈Term L₁ρ₁ᵇ
  ob₁ᵇ = solve! ρ₂R₁ᵇ L₁ρ₁ᵇ refl

  ob₂ᵇ : R₂ᵇ ≈Term L₂ρ₂ᵇ
  ob₂ᵇ = solve! R₂ᵇ L₂ρ₂ᵇ refl

-- the obligations at the segment statements (pure-assoc bridges)
ob₀ : (ρ₁ᵗ ∘ R₀ᵗ) ≈Term L₀ᵗ
ob₀ = ≈-Term-trans (assoc! (ρ₁ᵗ ∘ R₀ᵗ) ρ₁R₀ᵇ refl)
      (≈-Term-trans ob₀ᵇ (assoc! L₀ᵇ L₀ᵗ refl))

ob₁ : (ρ₂ᵗ ∘ R₁ᵗ) ≈Term (L₁ᵗ ∘ ρ₁ᵗ)
ob₁ = ≈-Term-trans (assoc! (ρ₂ᵗ ∘ R₁ᵗ) ρ₂R₁ᵇ refl)
      (≈-Term-trans ob₁ᵇ (assoc! L₁ρ₁ᵇ (L₁ᵗ ∘ ρ₁ᵗ) refl))

ob₂ : R₂ᵗ ≈Term (L₂ᵗ ∘ ρ₂ᵗ)
ob₂ = ≈-Term-trans (assoc! R₂ᵗ R₂ᵇ refl)
      (≈-Term-trans ob₂ᵇ (assoc! L₂ρ₂ᵇ (L₂ᵗ ∘ ρ₂ᵗ) refl))

-- The assembled segment-level equality.
segments : (R₂ᵗ ∘ R₁ᵗ ∘ R₀ᵗ) ≈Term (L₂ᵗ ∘ L₁ᵗ ∘ L₀ᵗ)
segments =
  ≈-Term-trans (∘-resp-≈ ob₂ ≈-Term-refl)
  (≈-Term-trans assoc
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl (∘-resp-≈ ob₁ ≈-Term-refl))
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)
               (∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl ob₀))))))
