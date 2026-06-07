{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- `unflatten : List X → ObjTerm`, the right-associated `unit`-padded
-- decoder.  `flatten ∘ unflatten` is propositionally `id`; the reverse
-- `unflatten ∘ flatten` holds only up to `≈Term`, so it is packaged as a
-- FreeMonoidal iso built from α/λ/ρ.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Unflatten (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.FromAPROP sig using (flatten)

open import Data.List using (List; []; _∷_; _++_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)

open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Utilities Monoidal-FreeMonoidal
  using (_⊗ᵢ_)
open import Categories.Morphism FreeMonoidal public
  using (_≅_; module ≅)

open Monoidal Monoidal-FreeMonoidal using (unitorˡ; unitorʳ; associator)

--------------------------------------------------------------------------------
-- `unflatten` is re-exported from `PermuteCoherence.Faithfulness` (same
-- definition over generic `FreeMonoidalData`) so SMC bridges observe
-- definitional equality between the two unflattens.

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData public
  using (unflatten; unflatten-++-≅)

--------------------------------------------------------------------------------
-- `flatten ∘ unflatten ≡ id` propositionally.

flatten-unflatten : ∀ l → flatten (unflatten l) ≡ l
flatten-unflatten []       = refl
flatten-unflatten (x ∷ xs) = cong (x ∷_) (flatten-unflatten xs)

--------------------------------------------------------------------------------
-- The reverse round-trip is a coherence iso, not a propositional equality.

unflatten-flatten-≈ : ∀ (A : ObjTerm) → A ≅ unflatten (flatten A)
unflatten-flatten-≈ unit     = ≅.refl
unflatten-flatten-≈ (Var x)  = ≅.sym unitorʳ
unflatten-flatten-≈ (A ⊗₀ B) =
  ≅.trans (unflatten-flatten-≈ A ⊗ᵢ unflatten-flatten-≈ B)
          (≅.sym (unflatten-++-≅ (flatten A) (flatten B)))
