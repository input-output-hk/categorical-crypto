{-# OPTIONS --safe --without-K #-}

module Categories.PermuteCoherence.FinBijSubst where

open import Data.List.Base using (List; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst)

open import Categories.PermuteCoherence.FinBij using (FinBij)
open import Categories.PermuteCoherence.Eval using (eval-↭)

open import Level using (Level)

private
  variable
    a : Level
    A : Set a

-- eval commutes with subst on the codomain.
eval-subst-cod : {xs : List A} {C D : List A} (eq : C ≡ D) (p : xs ↭ C)
  → eval-↭ (subst (λ z → xs ↭ z) eq p)
    ≡ subst (λ n → FinBij (length xs) n) (cong length eq) (eval-↭ p)
eval-subst-cod refl p = refl
