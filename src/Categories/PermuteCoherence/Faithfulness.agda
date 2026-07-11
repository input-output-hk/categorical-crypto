{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Faithfulness of `eval-↭`: list-permutation derivations agreeing on
-- their evaluated finite bijection produce ≈Term-equal `permute` terms
-- in the free symmetric monoidal category.
--
-- Parameterised over `FreeMonoidalData`, so the generic `permute` is
-- reusable in any free (symmetric) monoidal category.  This module
-- exposes the generic `unflatten`/`permute` definitions plus the
-- `α⇐-comm`/`unflatten-++-≅` coherence helpers; the faithfulness proof
-- itself lives in `FaithfulnessInductive`.
------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.PermuteCoherence.Faithfulness
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d
open FreeMonoidalData d using (X)

open import Data.List.Base using (List; []; _∷_; _++_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

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
