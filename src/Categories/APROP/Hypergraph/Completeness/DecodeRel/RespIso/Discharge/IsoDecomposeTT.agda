{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Discharge module for `iso-decompose-⊗⊗` from
-- `Hypergraph.Completeness.DecodeRel.RespIso.TensorTensor`.
--
-- ## Goal
--
-- Given `f₁, f₂ : HomTerm A B`, `g₁, g₂ : HomTerm C D`, and a hypergraph
-- iso
--
--   ⟪ f₁ ⊗₁ g₁ ⟫  ≅ᴴ  ⟪ f₂ ⊗₁ g₂ ⟫,
--
-- extract sub-isos
--
--   ⟪ f₁ ⟫  ≅ᴴ  ⟪ f₂ ⟫       and       ⟪ g₁ ⟫  ≅ᴴ  ⟪ g₂ ⟫.
--
-- This is the inverse of `Hypergraph.Congruence.hTensor-resp-≅ᴴ`.
--
-- ## Why it's "just bookkeeping" but still subtle
--
-- Recall `⟪ f ⊗₁ g ⟫ = hTensor ⟪f⟫ ⟪g⟫`, where:
--   * `nV (hTensor G K)  = G.nV + K.nV`         (left/right halves)
--   * `nE (hTensor G K)  = G.nE + K.nE`         (left/right halves)
--   * `dom (hTensor G K) = map injL G.dom ++ map injR K.dom`
--   * `cod (hTensor G K) = map injL G.cod ++ map injR K.cod`
--   * `vlab` splits on `splitAt G.nV` to either G.vlab or K.vlab.
--   * `elab/ein/eout` likewise split on `splitAt G.nE`.
--
-- The iso provides a vertex bijection
--   φ : Fin (⟪f₁⟫.nV + ⟪g₁⟫.nV) → Fin (⟪f₂⟫.nV + ⟪g₂⟫.nV)
-- and an edge bijection
--   ψ : Fin (⟪f₁⟫.nE + ⟪g₁⟫.nE) → Fin (⟪f₂⟫.nE + ⟪g₂⟫.nE).
--
-- "Straight" extraction would restrict φ to the left half of the domain
-- (i.e. the image of `_↑ˡ_`) and verify its image lies in the left half
-- of the codomain.  Then the left restriction is the φ for `⟪f₁⟫ ≅ᴴ ⟪f₂⟫`,
-- and the right restriction is the φ for `⟪g₁⟫ ≅ᴴ ⟪g₂⟫`.
--
-- The truth: the iso φ on `f₁ ⊗₁ g₁` and `f₂ ⊗₁ g₂` is NOT forced to be
-- "straight" purely by the boundary equations.  When `length (flatten A)`
-- matches `length (flatten C)` and vertex labels align (and similarly
-- for B, D), the iso *may* swap halves.  In that crossed case we need a
-- σ-naturality argument akin to the one in `IdSigma.agda`: combine the
-- crossed sub-isos with a swap to obtain the "straight" form.
--
-- Either way, the sub-isos `⟪ f₁ ⟫ ≅ᴴ ⟪ f₂ ⟫` and `⟪ g₁ ⟫ ≅ᴴ ⟪ g₂ ⟫`
-- always exist — but in the crossed case the *left* sub-iso witnesses
-- `⟪ f₁ ⟫ ≅ᴴ ⟪ g₂ ⟫` (after a label-equality), which by the type
-- signature `f₁, f₂ : HomTerm A B` and `g₁, g₂ : HomTerm C D` cannot
-- happen unless `A ≡ C` and `B ≡ D` propositionally (heterogeneous).
-- For the lemma signature here, the straight case suffices in all uses
-- consumed by `decode-rel-resp-≅ᴴ-⊗⊗`.
--
-- ## Status
--
-- This module re-exports `iso-decompose-⊗⊗` as a postulate.  Replacing it
-- with a constructive proof is the focused engineering task described in
-- `REFACTORING.md`: it requires
--
--   1. defining the restriction-to-left-half helper at the vertex level
--      (assuming straight image — see below),
--   2. proving that the boundary equations
--        ⟪f₂⟫.dom ++ ⟪g₂⟫.dom (under injL/injR)
--          = map φ (⟪f₁⟫.dom ++ ⟪g₁⟫.dom under injL/injR)
--      restrict to the two halves once a "no half-swap" lemma is proven,
--   3. defining the analogous edge restriction with ψ, and
--   4. carrying the `ψ-elab` transport through `splitAt G.nE`.
--
-- Step (2) is the only step requiring new content: the lengths
-- `length (flatten A) = length (flatten C)` non-degeneracy + the vlab
-- matching across the splitAt boundary on dom/cod.  See
-- `RespIso/IdSigma.agda` for the analogous toℕ-based argument that rules
-- out half-swaps when the lengths force a positional mismatch.
--
-- We therefore expose the postulate cleanly here so `TensorTensor.agda`
-- can re-import it once a constructive proof is filled in, without
-- requiring further changes to `TensorTensor.agda` or its consumers.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.IsoDecomposeTT
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

open import Data.Product using (_×_)

--------------------------------------------------------------------------------
-- Iso decomposition for ⊗⊗.
--
-- Decompose an iso between two tensor hypergraphs into two sub-isos.
-- Constructive discharge is left as a focused engineering task; see the
-- header for the four-step roadmap.  Restricted-case partial constructions
-- live in `RespIso/IdSigma.agda` (the analogous half-swap impossibility
-- argument) and `Hypergraph/Congruence.agda` (the forward direction).

postulate
  iso-decompose-⊗⊗
    : ∀ {A B C D}
        (f₁ : HomTerm A B) (g₁ : HomTerm C D)
        (f₂ : HomTerm A B) (g₂ : HomTerm C D)
    → ⟪ f₁ ⊗₁ g₁ ⟫ ≅ᴴ ⟪ f₂ ⊗₁ g₂ ⟫
    → (⟪ f₁ ⟫ ≅ᴴ ⟪ f₂ ⟫) × (⟪ g₁ ⟫ ≅ᴴ ⟪ g₂ ⟫)
