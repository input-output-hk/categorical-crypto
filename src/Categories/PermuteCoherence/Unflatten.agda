{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Right-associated, unit-padded interpretation of lists and their permutations.
------------------------------------------------------------------------

open import Data.List.Base using (List; _++_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Level

open import Categories.FreeMonoidal

module Categories.PermuteCoherence.Unflatten
  {ℓ′ : Level} (d : FreeMonoidalData {ℓ′}) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d
open import Categories.Morphism FreeMonoidal
open FreeMonoidalData d

-- `FreeMonoidal d` hides the wire kit from its public namespace.
open FreeMonoidalHelper v X using (wires)
open FreeMonoidalHelper.Mor v X mor using (merge; split; merge∘split; split∘merge)

unflatten : List X → ObjTerm
unflatten = wires

unflatten-++-≅ : ∀ (xs ys : List X) → unflatten (xs ++ ys) ≅ unflatten xs ⊗₀ unflatten ys
unflatten-++-≅ xs ys = record
  { from = split xs ; to = merge xs
  ; iso = record { isoˡ = merge∘split xs ; isoʳ = split∘merge xs } }

permute : ∀ {xs ys : List X} → xs Perm.↭ ys → HomTerm (unflatten xs) (unflatten ys)
permute Perm.refl         = id
permute (Perm.prep x p)   = id ⊗₁ permute p
permute (Perm.swap x y p) = (id ⊗₁ (id ⊗₁ permute p)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
permute (Perm.trans p q)  = permute q ∘ permute p
