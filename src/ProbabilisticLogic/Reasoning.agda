{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude

open import Class.HasOrder
open import Relation.Binary using (Rel)

module ProbabilisticLogic.Reasoning where

import Relation.Binary.Reasoning.PartialOrder as ≤-Reasoning'

module ≤-Reasoning {a ℓ₁ ℓ₂ ℓ₃} (A : Type a) {_≈_ : Rel A ℓ₁}
  ⦃ po : HasPartialOrder {a} {A} {ℓ₁} {_≈_} {ℓ₂} {ℓ₃} ⦄ where
  open ≤-Reasoning' record { isPartialOrder = ≤-isPartialOrder {A = A} } public
