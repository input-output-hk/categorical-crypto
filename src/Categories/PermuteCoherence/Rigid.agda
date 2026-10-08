{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- On a `Unique` codomain, lookup is injective, so lookup-soundness forces
-- the evaluated position bijection.  Labels themselves need not be injective.
------------------------------------------------------------------------

module Categories.PermuteCoherence.Rigid where

open import Categories.PermuteCoherence.Eval
open import Categories.PermuteCoherence.FinBij

open import Data.Fin.Base
open import Data.Fin.Patterns
import Data.Fin.Permutation as P
open import Data.List.Base
open import Data.List.Properties.Ext
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional
open import Level
open import Relation.Binary.PropositionalEquality

private
  variable
    a : Level
    A : Set a

infix 4 _≅↭_
_≅↭_ : {xs ys : List A} → xs ↭ ys → xs ↭ ys → Set
p ≅↭ q = eval-↭ p ≈-fb eval-↭ q

lookup-sound
  : {xs ys : List A} (p : xs ↭ ys) (i : Fin (length xs))
  → lookup ys (eval-↭ p P.⟨$⟩ʳ i) ≡ lookup xs i
lookup-sound Perm.refl         i             = refl
lookup-sound (Perm.prep x p)   0F            = refl
lookup-sound (Perm.prep x p)   (suc i)       = lookup-sound p i
lookup-sound (Perm.swap x y p) 0F            = refl
lookup-sound (Perm.swap x y p) (suc 0F)      = refl
lookup-sound (Perm.swap x y p) (suc (suc i)) = lookup-sound p i
lookup-sound (Perm.trans p q)  i             =
  trans (lookup-sound q (eval-↭ p P.⟨$⟩ʳ i)) (lookup-sound p i)

eval-rigid : {xs ys : List A} → Unique ys → (p q : xs ↭ ys) → p ≅↭ q
eval-rigid uniq p q i =
  lookup-injective-unique uniq _ _
    (trans (lookup-sound p i) (sym (lookup-sound q i)))
