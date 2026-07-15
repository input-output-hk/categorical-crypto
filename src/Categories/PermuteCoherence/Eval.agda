{-# OPTIONS --safe --cubical-compatible #-}

------------------------------------------------------------------------
-- Evaluation of list-permutation derivations into finite bijections.
--
-- Given a derivation `r : xs ↭ ys` of `Data.List.Relation.Binary.
-- Permutation.Propositional._↭_`, `eval-↭ r` is a bijection between the
-- positions of `xs` and `ys`.
------------------------------------------------------------------------

module Categories.PermuteCoherence.Eval where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

open import Categories.PermuteCoherence.FinBij

open import Level using (Level)

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- The main evaluation function.

eval-↭ : {xs ys : List A} (r : xs ↭ ys) → FinBij (length xs) (length ys)
eval-↭ Perm.refl         = id-fb
eval-↭ (Perm.prep _ p)   = cons-fb (eval-↭ p)
eval-↭ (Perm.swap _ _ p) = swap-fb _ ∘-fb cons-fb (cons-fb (eval-↭ p))
eval-↭ (Perm.trans p q)  = eval-↭ q ∘-fb eval-↭ p
