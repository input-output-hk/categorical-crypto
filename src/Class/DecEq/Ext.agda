{-# OPTIONS --safe --without-K #-}

-- What a definition branching on a decided equality needs in order to reduce
-- at an ABSTRACT argument: the Boolean value of the reflexive case.  Without
-- it `if ⌊ x ≟ x ⌋ then _ else _` is stuck for every `x` that is not a literal.

open import Class.DecEq

open import Data.Bool.Base
open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

module Class.DecEq.Ext where

private variable
  ℓ : Level
  A : Set ℓ

≟-refl : ⦃ _ : DecEq A ⦄ (x : A) → ⌊ x ≟ x ⌋ ≡ true
≟-refl x = trans (isYes≗does (x ≟ x)) (dec-true (x ≟ x) refl)
