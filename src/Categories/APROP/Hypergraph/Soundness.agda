{-# OPTIONS --safe --without-K #-}

-- Soundness is reflected from the presented strict SMC through the
-- strictification round-trip and bridge cancellation.

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Iso
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)

import Categories.APROP.Hypergraph.Soundness.Strict.Soundness sig as SA

opaque
  soundness : ∀ {A B} {f g : HomTerm A B} → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g
  soundness = SA.soundness-strict
