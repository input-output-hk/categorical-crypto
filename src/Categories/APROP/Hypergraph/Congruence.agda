{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- DE-INDEXED REFACTOR — TEMPORARY POSTULATE STUB.
--
-- Original Congruence.agda was a 719-line proof of `hTensor-resp-≅ᴴ`
-- and `hCompose-resp-≅ᴴ` structured around indexed `Hypergraph`'s
-- subst₂ chains for `ψ-elab` (six `subst₂-trans` collapses) and the
-- `remap-comm` lemma (decidable-equality with-blocks under fixed
-- boundary indices).  Migrating to the de-indexed setting is mechanical
-- but voluminous follow-up.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Congruence (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; hTensor)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

postulate
  hTensor-resp-≅ᴴ
    : {G₁ G₂ K₁ K₂ : Hypergraph FlatGen}
    → G₁ ≅ᴴ G₂ → K₁ ≅ᴴ K₂
    → hTensor G₁ K₁ ≅ᴴ hTensor G₂ K₂
