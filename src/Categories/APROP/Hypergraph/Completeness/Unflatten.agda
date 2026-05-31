{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 3.5a — `unflatten` and round-trip on the boundary.
--
-- `unflatten : List X → ObjTerm` is the right-associated, `unit`-padded
-- decoder.  The composition `flatten ∘ unflatten` is propositionally the
-- identity on `List X`; the other direction `unflatten ∘ flatten` is only
-- equal up to `≈Term`, so we package it as an iso in the FreeMonoidal
-- category (built from α/λ/ρ).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Unflatten (sig : APROPSignature) where

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
-- Decode a flat atom list into a right-associated `ObjTerm`.
--
-- Re-exported from `Categories.PermuteCoherence.Faithfulness` (which has
-- the same definition over generic `FreeMonoidalData`) so that downstream
-- bridges to generic SMC infrastructure observe definitional equality
-- between the two unflattens.

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
