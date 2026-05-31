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

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; sym)

open import Categories.PermuteCoherence.FinBij

open import Level using (Level)

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Length preservation (re-exporting the stdlib lemma inline; kept local
-- to avoid importing the whole `Properties` file).

↭-length : {xs ys : List A} → xs ↭ ys → length xs ≡ length ys
↭-length Perm.refl            = refl
↭-length (Perm.prep _ p)      = cong suc (↭-length p)
↭-length (Perm.swap _ _ p)    = cong (λ n → suc (suc n)) (↭-length p)
↭-length (Perm.trans p q)     = trans-≡ (↭-length p) (↭-length q)
  where
  trans-≡ : ∀ {n m k : ℕ} → n ≡ m → m ≡ k → n ≡ k
  trans-≡ refl q = q

------------------------------------------------------------------------
-- The main evaluation function.

eval-↭ : {xs ys : List A} (r : xs ↭ ys) → FinBij (length xs) (length ys)
eval-↭ Perm.refl         = id-fb
eval-↭ (Perm.prep _ p)   = cons-fb (eval-↭ p)
eval-↭ (Perm.swap _ _ p) = swap-fb _ ∘-fb cons-fb (cons-fb (eval-↭ p))
eval-↭ (Perm.trans p q)  = eval-↭ q ∘-fb eval-↭ p

------------------------------------------------------------------------
-- Utility lemmas

eval-↭-refl : {xs : List A} → eval-↭ (Perm.refl {xs = xs}) ≡ id-fb {n = length xs}
eval-↭-refl = refl

eval-↭-prep : ∀ {xs ys : List A} (x : A) (p : xs ↭ ys) →
              eval-↭ (Perm.prep x p) ≡ cons-fb (eval-↭ p)
eval-↭-prep _ _ = refl

eval-↭-trans : ∀ {xs ys zs : List A} (p : xs ↭ ys) (q : ys ↭ zs) →
               eval-↭ (Perm.trans p q) ≡ eval-↭ q ∘-fb eval-↭ p
eval-↭-trans _ _ = refl
