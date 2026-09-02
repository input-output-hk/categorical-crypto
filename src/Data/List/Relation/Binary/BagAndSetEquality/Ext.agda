{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Extensions to `Data.List.Relation.Binary.BagAndSetEquality`.
------------------------------------------------------------------------

open import Data.List.Base using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.BagAndSetEquality using (_∼[_]_; set)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function.Bundles
open import Level
open import Relation.Binary.PropositionalEquality

module Data.List.Relation.Binary.BagAndSetEquality.Ext where

private variable a : Level
                 A : Set a
                 x : A
                 xs : List A

-- Consing on an element the list already has changes no membership.  The stdlib
-- proves only `x ∷ x ∷ [] ∼[ set ] [ x ]`, and only inside a private proof.
∷-absorb : x ∈ xs → (x ∷ xs) ∼[ set ] xs
∷-absorb x∈xs = mk⇔ (λ where (here refl)  → x∈xs
                             (there z∈xs) → z∈xs) there
