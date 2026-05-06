{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- DE-INDEXED REFACTOR — TEMPORARY POSTULATE STUB.
--
-- Original proof was structured around:
--   * hCompose-hId-R-iso-generic peeling subst₂-wrapped hIds.
--   * hTensor-subst₂-left commuting subst₂ across hTensor.
-- Under de-indexing, both subst₂s on Hypergraph are gone.  The
-- triangle theorem still holds, but its proof needs reformulating.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Triangle (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

postulate
  triangle-sound
    : ∀ {A B}
    → ⟪ id {A} ⊗₁ λ⇒ {B} ∘ α⇒ {A} {unit} {B} ⟫
    ≅ᴴ ⟪ ρ⇒ {A} ⊗₁ id {B} ⟫
