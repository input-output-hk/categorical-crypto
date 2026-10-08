{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- All consumers share the search definition, including its returned derivation.
--------------------------------------------------------------------------------

module Categories.Combinatorics.ExtractPrefix where

open import Data.Fin
open import Data.List
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

private
  variable
    n : ℕ

extract-elem
  : (k : Fin n) (xs : List (Fin n))
  → Maybe (Σ[ rest ∈ List (Fin n) ] xs Perm.↭ k ∷ rest)
extract-elem k []       = nothing
extract-elem k (x ∷ xs) = case x ≟ k of λ where
  (yes p) → just (xs , subst (λ y → (x ∷ xs) Perm.↭ y ∷ xs) p Perm.refl)
  (no _) → case extract-elem k xs of λ where
    nothing → nothing
    (just (rest , q)) →
      just (x ∷ rest , Perm.trans (Perm.prep x q) (Perm.swap x k Perm.refl))

extract-prefix
  : (ks xs : List (Fin n))
  → Maybe (Σ[ rest ∈ List (Fin n) ] xs Perm.↭ ks ++ rest)
extract-prefix []       xs = just (xs , Perm.refl)
extract-prefix (k ∷ ks) xs = case extract-elem k xs of λ where
  nothing → nothing
  (just (xs' , p)) → case extract-prefix ks xs' of λ where
    nothing → nothing
    (just (rest , q)) → just (rest , Perm.trans p (Perm.prep k q))

extract-exact : (ks xs : List (Fin n)) → Maybe (xs Perm.↭ ks)
extract-exact ks xs = case extract-prefix ks xs of λ where
  nothing → nothing
  (just ([] , p)) → just (Perm.trans p (PermProp.++-identityʳ ks))
  (just (_ ∷ _ , _)) → nothing
