{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Phases 3.5c-d (and the missing piece of 3.5e) — `decode` and its
-- properties.
--
-- `decode` reconstructs a HomTerm from a translated hypergraph
-- `⟪ f ⟫` (Phase 3.5c).  Its constructive cospan-form algorithm
-- lives in `Decode.agda` and is exposed as
-- `decode-attempt : Hypergraph → Maybe HomTerm`.  The `Maybe` is
-- discharged by `decode-attempt-Linear` in `DecodeAttempt.agda`, which
-- is a *constructive* proof for translated hypergraphs by induction on
-- the term — relying on per-smart-constructor postulates that are
-- placeholders for the eventually-fully-constructive cases.
--
-- Two further properties — both currently postulated — make `decode`
-- useful for completeness:
--
--   * ~decode-roundtrip~ (Phase 3.5d): on a translated term,
--     ~decode f ≈Term bridge f~, where ~bridge~ is ~f~ composed with
--     the ~unflatten-flatten-≈~ coherence iso on each side.
--     Constructive proof is by induction on ~f~ (~3-5 days).
--
--   * ~decode-resp-≅ᴴ~ (consumed by Phase 3.5e):
--     ~⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → decode f ≈Term decode g~.  Constructive
--     proof might be possible directly by induction on the hypergraph
--     iso (without going through canonical form — see TODO.org
--     Phase 3.5b open question).
--
-- The cospan-form algorithm from TensorRocq §3.2 (now constructive
-- in `Decode.agda`):
--
--   1. Initial stack `s = H.dom`.
--   2. For each edge `e : Fin H.nE` in natural Fin order:
--      a. Search for `H.ein e` as a sub-multiset prefix of `s`;
--         on success, permute and apply `Agen (elab e) ⊗₁ id`.
--         On failure, fall back to identity (skip the edge).
--      b. Update `s` to `H.eout e ++ rest`.
--   3. Final search for `H.cod` in the end-of-edges stack; if found
--      with empty residual, apply the resulting permutation.
--
-- Linearity (each vertex appears exactly once on each side of every
-- ein/eout/dom/cod position) means only symmetries are needed for the
-- reshuffles — no duplication or discarding primitives are required.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Decoder (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; ⟪_⟫; flatten)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear) public
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab) public
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (decode-attempt; extract-elem; extract-prefix; extract-exact;
         Agen-edge; edge-step; process-all-edges) public
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-elem-self; extract-elem-skip-nothing; extract-elem-skip-just;
         extract-elem-↑ʳ-on-↑ˡ-list; extract-elem-↑ˡ-on-↑ʳ-list;
         extract-prefix-[]; extract-prefix-self; extract-exact-self) public
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode-attempt-hEmpty; decode-attempt-hVar;
         decode-attempt-hSwap; decode-attempt-hGen; decode-attempt-hId;
         decode-attempt-hTensor; decode-attempt-hCompose;
         decode-attempt-subst₂; decode-attempt-Linear;
         decode; bridge) public
open import Categories.APROP.Hypergraph.Completeness.DecodeRoundtrip sig
  using (decode-roundtrip;
         decode-roundtrip-Agen; decode-roundtrip-id;
         decode-roundtrip-∘; decode-roundtrip-⊗₁;
         decode-roundtrip-λ⇒; decode-roundtrip-λ⇐;
         decode-roundtrip-ρ⇒; decode-roundtrip-ρ⇐;
         decode-roundtrip-α⇒; decode-roundtrip-α⇐;
         decode-roundtrip-σ) public

open import Data.List using (List)

private
  variable
    As Bs : List X

--------------------------------------------------------------------------------
-- The remaining property of decode (still postulated): preservation
-- of hypergraph isomorphism.

postulate
  -- decode preserves hypergraph iso (consumed by Phase 3.5e).
  -- Stated for translated hypergraphs since `decode` itself takes a term.
  decode-resp-≅ᴴ
    : ∀ {A B} (f g : HomTerm A B)
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → decode f ≈Term decode g
