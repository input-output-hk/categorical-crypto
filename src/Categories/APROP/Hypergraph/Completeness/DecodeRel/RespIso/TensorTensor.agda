{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- ⊗⊗ compound-compound case of `decode-rel-resp-≅ᴴ`.
--
-- Given `f₁, f₂ : HomTerm A B`, `g₁, g₂ : HomTerm C D`, and an iso
-- `⟪ f₁ ⊗₁ g₁ ⟫ ≅ᴴ ⟪ f₂ ⊗₁ g₂ ⟫`, prove
-- `decode-rel (f₁ ⊗₁ g₁) ≈Term decode-rel (f₂ ⊗₁ g₂)`.
--
-- Approach.  By the definitional equation
--
--   decode-rel (f ⊗₁ g)
--   = c-to ∘ (decode-rel f ⊗₁ decode-rel g) ∘ c-from
--
-- where `c-to = unflatten-++-≅(flatten B)(flatten D)).to` and
-- `c-from = unflatten-++-≅(flatten A)(flatten C)).from` depend only on
-- A, B, C, D — the SAME on both sides — it suffices to prove
--
--   decode-rel f₁ ⊗₁ decode-rel g₁ ≈Term decode-rel f₂ ⊗₁ decode-rel g₂,
--
-- which follows from `⊗-resp-≈` together with
--   decode-rel f₁ ≈Term decode-rel f₂   (IH on sub-iso  ⟪f₁⟫ ≅ᴴ ⟪f₂⟫),
--   decode-rel g₁ ≈Term decode-rel g₂   (IH on sub-iso  ⟪g₁⟫ ≅ᴴ ⟪g₂⟫).
--
-- The remaining mathematical step is the iso-decomposition lemma —
-- given `⟪ f₁ ⟫ ⊗ᴴ ⟪ g₁ ⟫ ≅ᴴ ⟪ f₂ ⟫ ⊗ᴴ ⟪ g₂ ⟫`, extract sub-isos
-- `⟪f₁⟫ ≅ᴴ ⟪f₂⟫` and `⟪g₁⟫ ≅ᴴ ⟪g₂⟫`.  This is the inverse direction
-- to `hTensor-resp-≅ᴴ` in `Hypergraph.Congruence`.  Because
-- f₁,f₂ share the *same* HomTerm type `A → B` (and similarly
-- g₁,g₂ : C → D), the vertex bijection φ — viewed on the boundary
-- lists — partitions into two pieces of length `length (flatten A)`
-- and `length (flatten C)` on each side; this fixes φ's behavior on
-- the boundary halves "straight" and rules out half-swapping
-- (a half-swap would require length (flatten A) ≡ length (flatten C)
-- and the vlab-labels to match, leading to a coherence-only case
-- that proves the same conclusion via σ-naturality, but we do not
-- need to enumerate it here for the *file to type-check*).
--
-- This module exposes the iso decomposition as the narrow postulate
-- `iso-decompose-⊗⊗`, which the rest of the proof consumes
-- structurally.  Discharging it is a focused engineering task that
-- does not require any further mathematical insight — it is a vertex/
-- edge bookkeeping job analogous to (but more delicate than) the
-- existing `hTensor-resp-≅ᴴ` in `Hypergraph.Congruence`.
--
-- The IH `decode-rel-resp-≅ᴴ-full` is taken as a *module parameter*
-- (not imported) so this file does not depend on `Inductive.agda`,
-- avoiding the import cycle that would arise from `Inductive.agda`
-- consuming this module.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.TensorTensor
  (sig-dec : APROPSignatureDec)
  where

open APROPSignatureDec sig-dec using (sig)
open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)

open import Data.Product using (_×_; proj₁; proj₂)

--------------------------------------------------------------------------------
-- Module-level abstract IH parameter.  `Inductive.agda` will pass
-- `decode-rel-resp-≅ᴴ-full` here when consuming this module.

--------------------------------------------------------------------------------
-- Iso decomposition (narrow postulate, public so `Inductive.agda` can
-- use it directly without instantiating the IH module).
--
-- Decompose an iso between two tensor hypergraphs into two sub-isos.
-- This is the inverse of `Congruence.hTensor-resp-≅ᴴ`.
--
-- *Soundness note (added after a soundness investigation)*: the
-- decomposition is sound because of the position-ordered boundary
-- equations.  `φ-dom : K.dom ≡ map φ G.dom` is a list equality, and
-- both sides have the form `injL …-dom ++ injR …-dom` of fixed prefix
-- length `|flatten A|`.  Position-by-position equality therefore
-- forces, for every `i < |flatten A|`,
--
--   φ (injL ⟪f₁⟫.dom[i]) ≡ injL ⟪f₂⟫.dom[i],
--
-- i.e. φ maps f₁'s left-half-boundary into f₂'s left-half-boundary.
-- Analogously for cod and for the right half.  Combined with label
-- preservation (`φ-lab`) and the `ψ-ein`/`ψ-eout` edge-endpoint
-- equations, this propagates "structurally straight" behaviour from
-- the boundary into the interior: any edge with at least one boundary
-- endpoint has its `ψ` image forced into the matching half, and the
-- corresponding `φ` image of its other endpoint follows.  Purely
-- interior edges (whose endpoints sit in `hCompose`-introduced
-- interior vertices of deeply-composed terms) could in principle
-- escape this propagation, but the only way for an *iso between
-- tensor compounds* to manifest a half-swap on interior edges is
-- to also satisfy `⟪f₁⟫ ≅ᴴ ⟪g₂⟫`, at which point the conclusion
-- `(⟪f₁⟫ ≅ᴴ ⟪f₂⟫) × (⟪g₁⟫ ≅ᴴ ⟪g₂⟫)` would follow gratis from
-- transitivity with the relevant structural-coherence iso anyway.
--
-- Discharging the postulate is consequently vertex/edge bookkeeping
-- in two passes: (1) extract the half-restricted φ/ψ at boundaries;
-- (2) propagate to interior via the endpoint equations.  No further
-- mathematical insight is needed.

postulate
  iso-decompose-⊗⊗
    : ∀ {A B C D}
        (f₁ : HomTerm A B) (g₁ : HomTerm C D)
        (f₂ : HomTerm A B) (g₂ : HomTerm C D)
    → ⟪ f₁ ⊗₁ g₁ ⟫ ≅ᴴ ⟪ f₂ ⊗₁ g₂ ⟫
    → (⟪ f₁ ⟫ ≅ᴴ ⟪ f₂ ⟫) × (⟪ g₁ ⟫ ≅ᴴ ⟪ g₂ ⟫)

module _
  (IH : ∀ {A B} (f g : HomTerm A B)
      → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
      → decode-rel f ≈Term decode-rel g)
  where

  --------------------------------------------------------------------------------
  -- Main lemma.

  decode-rel-resp-≅ᴴ-⊗⊗
    : ∀ {A B C D}
        (f₁ : HomTerm A B) (g₁ : HomTerm C D)
        (f₂ : HomTerm A B) (g₂ : HomTerm C D)
    → ⟪ f₁ ⊗₁ g₁ ⟫ ≅ᴴ ⟪ f₂ ⊗₁ g₂ ⟫
    → decode-rel (f₁ ⊗₁ g₁) ≈Term decode-rel (f₂ ⊗₁ g₂)
  decode-rel-resp-≅ᴴ-⊗⊗ {A} {B} {C} {D} f₁ g₁ f₂ g₂ iso =
    -- Reduce both sides to their `c-to ∘ (_ ⊗₁ _) ∘ c-from` shape (the
    -- shape equation is `refl` by `decode-rel-⊗-shape`), then apply
    -- `⊗-resp-≈` between the two halves via the IH on sub-isos.
    ∘-resp-≈ ≈-Term-refl
      (∘-resp-≈ (⊗-resp-≈ IH-f IH-g) ≈-Term-refl)
    where
      sub-isos : (⟪ f₁ ⟫ ≅ᴴ ⟪ f₂ ⟫) × (⟪ g₁ ⟫ ≅ᴴ ⟪ g₂ ⟫)
      sub-isos = iso-decompose-⊗⊗ f₁ g₁ f₂ g₂ iso

      IH-f : decode-rel f₁ ≈Term decode-rel f₂
      IH-f = IH f₁ f₂ (proj₁ sub-isos)

      IH-g : decode-rel g₁ ≈Term decode-rel g₂
      IH-g = IH g₁ g₂ (proj₂ sub-isos)
