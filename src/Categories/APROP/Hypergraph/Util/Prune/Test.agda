{-# OPTIONS --safe --without-K #-}

module Categories.APROP.Hypergraph.Util.Prune.Test where

open import Categories.APROP.Hypergraph.Util.Prune
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

private
  duplicate : List (Fin 4)
  duplicate = suc zero ∷ zero ∷ suc zero ∷ []
  aligned : List (Fin 3)
  aligned = suc (suc zero) ∷ zero ∷ suc zero ∷ []
  allBoundary : List (Fin 3)
  allBoundary = suc (suc zero) ∷ zero ∷ suc zero ∷ []
  permuted : List (Fin 3)
  permuted = zero ∷ suc (suc zero) ∷ suc zero ∷ []

-- Duplicates retain the first occurrence, including when later matches have
-- different target vertices. Missing vertices retain their ascending rank.
first-occurrence-and-complement : map (toℕ ∘ remap-lookup duplicate aligned refl) (allFin 4)
                               ≡ 0 ∷ 2 ∷ 3 ∷ 4 ∷ []
first-occurrence-and-complement = refl

empty-seam : map (toℕ ∘ remap-lookup {m = 2} [] [] refl) (allFin 3) ≡ 2 ∷ 3 ∷ 4 ∷ []
empty-seam = refl

full-permuted-seam : map (toℕ ∘ remap-lookup allBoundary permuted refl) (allFin 3)
                   ≡ 2 ∷ 1 ∷ 0 ∷ []
full-permuted-seam = refl
