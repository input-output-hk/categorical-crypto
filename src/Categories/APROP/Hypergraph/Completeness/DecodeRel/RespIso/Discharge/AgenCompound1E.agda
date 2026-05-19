{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Discharge module for `decode-rel-resp-≅ᴴ-Agen-compound-1E` from
-- `Hypergraph.Completeness.DecodeRel.RespIso.AtomicCompound`.
--
-- ## Goal
--
-- Given `g : mor A B` and a compound `h : HomTerm A B` with `nE ⟪h⟫ ≡ 1`
-- and an iso `⟪ Agen g ⟫ ≅ᴴ ⟪ h ⟫`, conclude
-- `decode-rel (Agen g) ≈Term decode-rel h`.
--
-- ## Strategy
--
-- Pattern-match on `h`'s outer constructor.
--
-- * `h = h₁ ∘ h₂` (so `nE ⟪h⟫ = nE ⟪h₂⟫ + nE ⟪h₁⟫ = 1`):
--
--     exactly one of `h₁`, `h₂` carries the unique edge, the other has
--     `nE ≡ 0`.  By Kelly coherence for the structural sub-term, its
--     `decode-rel` is a coherence morphism that collapses against the
--     non-trivial side, reducing the goal to
--     `decode-rel (Agen g) ≈Term decode-rel hₙₜ`, which is delivered by
--     the abstract inductive hypothesis `IH` applied to the sub-iso
--     extracted from the iso on the composite.
--
-- * `h = h₁ ⊗₁ h₂` (so `nE ⟪h⟫ = nE ⟪h₁⟫ + nE ⟪h₂⟫ = 1`):
--
--     same edge-budget split.  Here both halves may still carry non-trivial
--     structural content (vertices/boundary), so we additionally rely on
--     a coherence lemma that says: tensoring a non-trivial `Agen g` with
--     a 0-edge structural piece preserves the result up to coherence,
--     matched against the corresponding shape on the `Agen` side via the
--     iso.
--
-- ## Status
--
-- The four shape-specific reductions (∘-left, ∘-right, ⊗-left, ⊗-right)
-- are exposed as narrow postulates.  Each is reducible to:
--   * the abstract IH parameter, applied to a sub-iso, plus
--   * a coherence-only equality on `decode-rel` of the 0-edge sub-term.
--
-- The top-level dispatcher is constructive: it pattern-matches on `h`
-- and on which half carries the unique edge (decided by `nE ⟪h_i⟫`).
-- The narrow postulates plug in at the leaves.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.AgenCompound1E
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; ⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)

open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.AtomicCompound sig-dec
  using (Compound; compound-∘; compound-⊗)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

--------------------------------------------------------------------------------
-- Local edge-count abbreviation.

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

private
  nE : Hypergraph FlatGen → ℕ
  nE = Hypergraph.nE

  -- `a + b ≡ 1` is either `a ≡ 1, b ≡ 0` or `a ≡ 0, b ≡ 1`.
  +-≡1-cases : ∀ (a b : ℕ) → a + b ≡ 1
             → (a ≡ 1 × b ≡ 0) ⊎ (a ≡ 0 × b ≡ 1)
  +-≡1-cases zero          (suc zero)       refl = inj₂ (refl , refl)
  +-≡1-cases (suc zero)    zero             refl = inj₁ (refl , refl)
  +-≡1-cases zero          zero             ()
  +-≡1-cases zero          (suc (suc _))    ()
  +-≡1-cases (suc zero)    (suc _)          ()
  +-≡1-cases (suc (suc _)) _                ()

--------------------------------------------------------------------------------
-- Module parameterised by the abstract inductive hypothesis `IH`, mirroring
-- the pattern in `RespIso/AtomicCompound.agda` (and used by
-- `DecodeRel.Inductive` once the postulate here is fully discharged).

module _
  (IH : ∀ {A B} (f g : HomTerm A B)
      → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
      → decode-rel f ≈Term decode-rel g)
  where

  --------------------------------------------------------------------------------
  -- Narrow shape-specific postulates.  Each captures a single coherence
  -- collapse + sub-iso extraction step.  The combined dispatcher is
  -- fully constructive given these.

  postulate
    -- h = h₁ ∘ h₂ with `nE ⟪h₁⟫ ≡ 1`, `nE ⟪h₂⟫ ≡ 0`.
    -- h₂ is 0-edge structural; its decode-rel is a coherence morphism that
    -- collapses, reducing the goal to `IH` on `Agen g` vs `h₁`.
    discharge-∘-left
      : ∀ {A B C} {g : mor A C}
          (h₁ : HomTerm B C) (h₂ : HomTerm A B)
      → nE ⟪ h₁ ⟫ ≡ 1
      → nE ⟪ h₂ ⟫ ≡ 0
      → ⟪ Agen g ⟫ ≅ᴴ ⟪ h₁ ∘ h₂ ⟫
      → decode-rel (Agen g) ≈Term decode-rel (h₁ ∘ h₂)

    -- h = h₁ ∘ h₂ with `nE ⟪h₁⟫ ≡ 0`, `nE ⟪h₂⟫ ≡ 1`.
    discharge-∘-right
      : ∀ {A B C} {g : mor A C}
          (h₁ : HomTerm B C) (h₂ : HomTerm A B)
      → nE ⟪ h₁ ⟫ ≡ 0
      → nE ⟪ h₂ ⟫ ≡ 1
      → ⟪ Agen g ⟫ ≅ᴴ ⟪ h₁ ∘ h₂ ⟫
      → decode-rel (Agen g) ≈Term decode-rel (h₁ ∘ h₂)

    -- h = h₁ ⊗₁ h₂ with `nE ⟪h₁⟫ ≡ 1`, `nE ⟪h₂⟫ ≡ 0`.
    -- h₂ is 0-edge structural; the tensor reduces (via coherence and IH on
    -- the left half) to a decoded `Agen g` shape matching the LHS.
    discharge-⊗-left
      : ∀ {A B C D} {g : mor (A ⊗₀ C) (B ⊗₀ D)}
          (h₁ : HomTerm A B) (h₂ : HomTerm C D)
      → nE ⟪ h₁ ⟫ ≡ 1
      → nE ⟪ h₂ ⟫ ≡ 0
      → ⟪ Agen g ⟫ ≅ᴴ ⟪ h₁ ⊗₁ h₂ ⟫
      → decode-rel (Agen g) ≈Term decode-rel (h₁ ⊗₁ h₂)

    -- h = h₁ ⊗₁ h₂ with `nE ⟪h₁⟫ ≡ 0`, `nE ⟪h₂⟫ ≡ 1`.
    discharge-⊗-right
      : ∀ {A B C D} {g : mor (A ⊗₀ C) (B ⊗₀ D)}
          (h₁ : HomTerm A B) (h₂ : HomTerm C D)
      → nE ⟪ h₁ ⟫ ≡ 0
      → nE ⟪ h₂ ⟫ ≡ 1
      → ⟪ Agen g ⟫ ≅ᴴ ⟪ h₁ ⊗₁ h₂ ⟫
      → decode-rel (Agen g) ≈Term decode-rel (h₁ ⊗₁ h₂)

  --------------------------------------------------------------------------------
  -- Top-level dispatcher.  Constructive case-split on `h`'s outer
  -- constructor and on which sub-term carries the unique edge.

  decode-rel-resp-≅ᴴ-Agen-compound-1E
    : ∀ {A B} {g : mor A B} {h : HomTerm A B}
    → Compound h
    → nE ⟪ h ⟫ ≡ 1
    → ⟪ Agen g ⟫ ≅ᴴ ⟪ h ⟫
    → decode-rel (Agen g) ≈Term decode-rel h
  decode-rel-resp-≅ᴴ-Agen-compound-1E
    {g = g} (compound-∘ h₁ h₂) h-nE≡1 iso
    -- `nE ⟪ h₁ ∘ h₂ ⟫ = nE ⟪h₂⟫ + nE ⟪h₁⟫` (see `nE-∘` in `AtomicCompound`).
    with +-≡1-cases (nE ⟪ h₂ ⟫) (nE ⟪ h₁ ⟫) h-nE≡1
  ... | inj₁ (h₂-≡1 , h₁-≡0) =
    discharge-∘-right {g = g} h₁ h₂ h₁-≡0 h₂-≡1 iso
  ... | inj₂ (h₂-≡0 , h₁-≡1) =
    discharge-∘-left {g = g} h₁ h₂ h₁-≡1 h₂-≡0 iso
  decode-rel-resp-≅ᴴ-Agen-compound-1E
    {g = g} (compound-⊗ h₁ h₂) h-nE≡1 iso
    -- `nE ⟪ h₁ ⊗₁ h₂ ⟫ = nE ⟪h₁⟫ + nE ⟪h₂⟫`.
    with +-≡1-cases (nE ⟪ h₁ ⟫) (nE ⟪ h₂ ⟫) h-nE≡1
  ... | inj₁ (h₁-≡1 , h₂-≡0) =
    discharge-⊗-left {g = g} h₁ h₂ h₁-≡1 h₂-≡0 iso
  ... | inj₂ (h₁-≡0 , h₂-≡1) =
    discharge-⊗-right {g = g} h₁ h₂ h₁-≡0 h₂-≡1 iso
