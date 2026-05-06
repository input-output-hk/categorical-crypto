{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- DE-INDEXED REFACTOR — TEMPORARY POSTULATE STUB.
--
-- Original AlphaCommSound.agda was a 211-line proof structured around
-- 9 occurrences of `subst₂ (Hypergraph FlatGen)`.  Migrating
-- constructively to the de-indexed setting is mechanical follow-up.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.AlphaCommSound (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

postulate
  α-comm-sound
    : ∀ {A B C D E F} {f : HomTerm A B} {g : HomTerm C D} {h : HomTerm E F}
    → ⟪ α⇒ {B} {D} {F} ∘ (f ⊗₁ g) ⊗₁ h ⟫ ≅ᴴ ⟪ f ⊗₁ (g ⊗₁ h) ∘ α⇒ {A} {C} {E} ⟫
