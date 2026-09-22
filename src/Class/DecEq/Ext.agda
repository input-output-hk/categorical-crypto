{-# OPTIONS --safe --without-K #-}

-- What a definition branching on a decided equality needs in order to reduce
-- at an ABSTRACT argument: the Boolean value of the reflexive case.  Without
-- it `if ⌊ x ≟ x ⌋ then _ else _` is stuck for every `x` that is not a literal.

open import Class.DecEq

open import Data.Bool.Base using (true)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable.Core using (⌊_⌋; yes; no)
open import Relation.Nullary.Negation.Core using (contradiction)

module Class.DecEq.Ext where

private variable
  ℓ : Level
  A : Set ℓ

≟-refl : ⦃ _ : DecEq A ⦄ (x : A) → ⌊ x ≟ x ⌋ ≡ true
≟-refl x with x ≟ x
... | yes _  = refl
... | no ¬eq = contradiction refl ¬eq
