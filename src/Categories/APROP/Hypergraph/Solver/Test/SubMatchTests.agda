{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Operational smoke tests for `subMatch`: each `refl` below forces the matcher
-- to *reduce* at type-check time, so a green file means the search genuinely
-- located (or correctly rejected) the embedding — not merely that the types
-- line up.
--
--   f : a₀ → a₁ , g : a₁ → a₂ , h : a₂ → a₀ .
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.Test.SubMatchTests where

open import Data.Bool.Base using (true; false)
open import Data.Maybe.Base using (is-just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.APROP using (module APROP)
open import Categories.APROP.Hypergraph.Solver.Test.ThreeGens
  using (a₁; f; g; h; mySig)

open import Categories.APROP.Hypergraph.Model.Translation mySig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.Rewrite.SubMatch mySig using (subMatch)
open APROP mySig

--------------------------------------------------------------------------------
-- Positive: the single edge `f` embeds in the chain `h ∘ (g ∘ f)`.

found-single : is-just (subMatch ⟪ Agen f ⟫ ⟪ Agen h ∘ (Agen g ∘ Agen f) ⟫) ≡ true
found-single = refl

-- Positive: the two-edge redex `g ∘ f` embeds in the chain `h ∘ (g ∘ f)`.
found-pair : is-just (subMatch ⟪ Agen g ∘ Agen f ⟫ ⟪ Agen h ∘ (Agen g ∘ Agen f) ⟫) ≡ true
found-pair = refl

-- Positive: a redex sitting inside a tensor context, `f ⊗ id`.
found-in-tensor : is-just (subMatch ⟪ Agen f ⟫ ⟪ Agen f ⊗₁ id {a₁} ⟫) ≡ true
found-in-tensor = refl

--------------------------------------------------------------------------------
-- Negative: a generator absent from the target is not matched.

absent : is-just (subMatch ⟪ Agen h ⟫ ⟪ Agen g ∘ Agen f ⟫) ≡ false
absent = refl
