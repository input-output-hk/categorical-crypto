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
--     `HomTerm (unflatten xs) (unflatten ys)`.
--
-- The combinatorial faithfulness core (`_≅↭ⁱ_`, `complete`) lives in
-- `PermuteCoherence.Coxeter.FaithfulnessInductive`, which does not depend on
-- this module.
------------------------------------------------------------------------

open import Categories.FreeMonoidal
open import Level

module Categories.PermuteCoherence.Unflatten
  {ℓ′ : Level} (d : FreeMonoidalData {ℓ′}) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d
open FreeMonoidalData d

open import Data.List.Base using (List; _++_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

open import Categories.Morphism FreeMonoidal

-- the wire kit, which `FreeMonoidal d`'s `hiding` list keeps out of the APROP
-- namespace (the solver stack opens `Mor` directly for the same reason)
open FreeMonoidalHelper v X using (wires)
open FreeMonoidalHelper.Mor v X mor using (merge; split; merge∘split; split∘merge)

------------------------------------------------------------------------
-- 1. Generic `unflatten` -- the right-associated, unit-padded decoder.
-- Definitionally `wires`, so SMC bridges observe the two as equal.
unflatten : List X → ObjTerm
unflatten = wires

------------------------------------------------------------------------
-- 1b. `unflatten` distributes over `_++_` up to a coherence iso: the
-- `split`/`merge` pair with its two cancellations.

unflatten-++-≅
  : ∀ (xs ys : List X)
  → unflatten (xs ++ ys) ≅ unflatten xs ⊗₀ unflatten ys
unflatten-++-≅ xs ys = record
  { from = split xs ; to = merge xs
  ; iso = record { isoˡ = merge∘split xs ; isoʳ = split∘merge xs } }

------------------------------------------------------------------------
-- 2. Generic `permute`.

permute : ∀ {xs ys : List X} → xs Perm.↭ ys → HomTerm (unflatten xs) (unflatten ys)
permute Perm.refl         = id
permute (Perm.prep x p)   = id ⊗₁ permute p
permute (Perm.swap x y p) =
  (id ⊗₁ (id ⊗₁ permute p)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
permute (Perm.trans p q)  = permute q ∘ permute p
