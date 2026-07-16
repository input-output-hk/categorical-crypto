{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Generic term-level building blocks for the free (symmetric) monoidal
-- decoder, parameterised over `FreeMonoidalData` so they are reusable in
-- any free (symmetric) monoidal category:
--
--   * `unflatten` / `unflatten-++-≅` : the right-associated, unit-padded
--     interpretation of a `List X` as an `ObjTerm`, and its distribution
--     over `_++_` up to a coherence iso;
--   * `permute` : a list-permutation derivation `xs ↭ ys` realised as a
--     `HomTerm (unflatten xs) (unflatten ys)`;
--   * `α⇐-comm` : dual-associator commutativity.
--
-- The combinatorial faithfulness core (`_≅↭ⁱ_`, `complete`) lives in
-- `FaithfulnessInductive`.
------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.PermuteCoherence.Faithfulness
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d
open FreeMonoidalData d using (X)

open import Data.List.Base using (List; []; _∷_; _++_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Utilities Monoidal-FreeMonoidal
  using (_⊗ᵢ_)
open import Categories.Morphism FreeMonoidal using (_≅_; module ≅)
open Monoidal Monoidal-FreeMonoidal using (unitorˡ; associator)

------------------------------------------------------------------------
-- 0. Dual associator commutativity, derived from `α-comm`:
--    α⇐ ∘ (h ⊗₁ (i ⊗₁ j)) ≈Term ((h ⊗₁ i) ⊗₁ j) ∘ α⇐.

α⇐-comm
  : ∀ {a b c a′ b′ c′ : ObjTerm}
      {h : HomTerm a a′} {i : HomTerm b b′} {j : HomTerm c c′}
  → α⇐ ∘ (h ⊗₁ (i ⊗₁ j)) ≈Term ((h ⊗₁ i) ⊗₁ j) ∘ α⇐
α⇐-comm {h = h} {i} {j} =
  ≈-Term-trans (≈-Term-sym idʳ)
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym α⇒∘α⇐≈id))
  (≈-Term-trans assoc
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl))
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)
  (≈-Term-trans (≈-Term-sym assoc)
  (≈-Term-trans (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl)
                 idˡ)))))))

------------------------------------------------------------------------
-- 1. Generic `unflatten` -- the right-associated, unit-padded decoder.

unflatten : List X → ObjTerm
unflatten []       = unit
unflatten (x ∷ xs) = Var x ⊗₀ unflatten xs

------------------------------------------------------------------------
-- 1b. `unflatten` distributes over `_++_` up to a coherence iso.

unflatten-++-≅
  : ∀ (xs ys : List X)
  → unflatten (xs ++ ys) ≅ unflatten xs ⊗₀ unflatten ys
unflatten-++-≅ []       ys = ≅.sym unitorˡ
unflatten-++-≅ (x ∷ xs) ys =
  ≅.trans (≅.refl ⊗ᵢ unflatten-++-≅ xs ys) (≅.sym associator)

------------------------------------------------------------------------
-- 2. Generic `permute`.

permute : ∀ {xs ys : List X} → xs Perm.↭ ys → HomTerm (unflatten xs) (unflatten ys)
permute Perm.refl         = id
permute (Perm.prep x p)   = id ⊗₁ permute p
permute (Perm.swap x y p) =
  (id ⊗₁ (id ⊗₁ permute p)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
permute (Perm.trans p q)  = permute q ∘ permute p
