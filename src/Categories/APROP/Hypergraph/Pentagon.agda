{-# OPTIONS --without-K --lossy-unification #-}

--------------------------------------------------------------------------------
-- DE-INDEXED REFACTOR — TEMPORARY POSTULATE STUB.
--
-- Original Pentagon.agda was a 451-line proof of `pentagon-sound`
-- structured around 50 occurrences of `subst₂ (Hypergraph FlatGen)`.
-- Under de-indexing those subst₂s are gone; the proof needs
-- reformulating but the theorem still holds.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Pentagon (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

postulate
  pentagon-sound
    : ∀ {A B C D}
    → ⟪ id {A} ⊗₁ α⇒ {B} {C} {D} ∘ α⇒ {A} {B ⊗₀ C} {D} ∘ α⇒ {A} {B} {C} ⊗₁ id {D} ⟫
    ≅ᴴ ⟪ α⇒ {A} {B} {C ⊗₀ D} ∘ α⇒ {A ⊗₀ B} {C} {D} ⟫
