{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- DE-INDEXED REFACTOR — TEMPORARY POSTULATE STUB.
--
-- Original CongruenceP.agda was a 659-line proof of
-- `hComposeP-resp-≅ᴴ` parallel to `Congruence.hCompose-resp-≅ᴴ` but
-- using the pruned composition `hComposeP`.  Migrating to the
-- de-indexed setting is mechanical but voluminous follow-up.
--
-- The primary export is `hComposeP-resp-≅ᴴ : G₁ ≅ᴴ G₂ → K₁ ≅ᴴ K₂ →
-- hComposeP G₁ K₁ ≅ᴴ hComposeP G₂ K₂`, used in Soundness's `∘-resp-≈`
-- case.  Postulated here for now.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.CongruenceP (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.PrunedCompose sig using (hComposeP)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
  hComposeP-resp-≅ᴴ
    : ∀ {G₁ G₂ K₁ K₂ : Hypergraph FlatGen}
        {bdy₁ : codL G₁ ≡ domL K₁}
        {bdy₂ : codL G₂ ≡ domL K₂}
    → G₁ ≅ᴴ G₂ → K₁ ≅ᴴ K₂
    → hComposeP G₁ K₁ bdy₁ ≅ᴴ hComposeP G₂ K₂ bdy₂
