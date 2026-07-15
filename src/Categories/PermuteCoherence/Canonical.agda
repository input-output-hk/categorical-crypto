{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Canonical equivalence of `_↭_` derivations.
--
-- `residual b` is the tail bijection obtained by removing the head of a
-- self-bijection.  `_≅↭_` relates two `_↭_` derivations that agree on
-- their evaluated finite bijection (via `eval-↭`).
------------------------------------------------------------------------

module Categories.PermuteCoherence.Canonical where

open import Data.Nat.Base
open import Data.Fin.Base
open import Data.Fin.Patterns
import Data.Fin.Permutation as P
open P
open import Data.List.Base using (List)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

open import Level using (Level)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Removing the head bijectively: `residual` is the bijection on the tail.

residual : ∀ {n} → (b : FinBij (suc n) (suc n)) → FinBij n n
residual b = remove 0F b

------------------------------------------------------------------------
-- Canonical equivalence: two derivations are canonically equivalent when
-- they agree on the underlying finite bijection.

infix 4 _≅↭_
_≅↭_ : {xs ys : List A} → xs ↭ ys → xs ↭ ys → Set
p ≅↭ q = eval-↭ p ≈-fb eval-↭ q
