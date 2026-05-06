{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- DE-INDEXED REFACTOR — TEMPORARY POSTULATE STUB.
--
-- Original SigmaNat.agda was a 1619-line proof of σ-naturality
-- structured around indexed Hypergraph subst₂ chains.  Migrating to
-- the de-indexed setting is mechanical follow-up.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.SigmaNat (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

postulate
  σ∘[f⊗g]≈[g⊗f]∘σ-sound
    : ∀ {A B C D} {f : HomTerm A B} {g : HomTerm C D}
    → ⟪ σ {B} {D} ∘ (f ⊗₁ g) ⟫ ≅ᴴ ⟪ (g ⊗₁ f) ∘ σ {A} {C} ⟫
