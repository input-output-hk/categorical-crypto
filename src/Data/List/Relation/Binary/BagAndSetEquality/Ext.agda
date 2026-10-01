{-# OPTIONS --safe --without-K #-}

open import Data.List.Base
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.BagAndSetEquality
open import Data.List.Relation.Unary.Any
open import Function.Bundles
open import Level
open import Relation.Binary.PropositionalEquality

module Data.List.Relation.Binary.BagAndSetEquality.Ext where

private variable a : Level
                 A : Set a
                 x : A
                 xs : List A

-- stdlib has only `x ∷ x ∷ [] ∼[ set ] [ x ]`, local to `¬-drop-cons`.
∷-absorb : x ∈ xs → (x ∷ xs) ∼[ set ] xs
∷-absorb x∈xs = mk⇔ (λ where (here refl)  → x∈xs
                             (there z∈xs) → z∈xs) there
