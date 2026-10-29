{-# OPTIONS --safe --cubical-compatible #-}

module Categories.PermuteCoherence.Eval where

open import Data.List.Base
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Level

open import Categories.PermuteCoherence.FinBij

private
  variable
    a : Level
    A : Set a

eval-↭ : {xs ys : List A} (r : xs ↭ ys) → FinBij (length xs) (length ys)
eval-↭ Perm.refl         = id-fb
eval-↭ (Perm.prep _ p)   = cons-fb (eval-↭ p)
eval-↭ (Perm.swap _ _ p) = swap-fb _ ∘-fb cons-fb (cons-fb (eval-↭ p))
eval-↭ (Perm.trans p q)  = eval-↭ q ∘-fb eval-↭ p
