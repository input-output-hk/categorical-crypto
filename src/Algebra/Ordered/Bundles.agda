{-# OPTIONS --safe --without-K #-}

-- Partially ordered (commutative) monoids

module Algebra.Ordered.Bundles where

open import Algebra.Core
open import Algebra.Structures
open import Level
open import Relation.Binary

record OrderedMonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field poset : Poset c ℓ₁ ℓ₂
  open Poset poset using (Carrier; _≈_; _≤_)
  field
    _∙_      : Op₂ Carrier
    ε        : Carrier
    isMonoid : IsMonoid _≈_ _∙_ ε
    ∙-mono   : Monotonic₂ _≤_ _≤_ _≤_ _∙_

record OrderedCommutativeMonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field poset : Poset c ℓ₁ ℓ₂
  open Poset poset using (Carrier; _≈_; _≤_)
  field
    _∙_                 : Op₂ Carrier
    ε                   : Carrier
    isCommutativeMonoid : IsCommutativeMonoid _≈_ _∙_ ε
    ∙-mono              : Monotonic₂ _≤_ _≤_ _≤_ _∙_

  orderedMonoid : OrderedMonoid c ℓ₁ ℓ₂
  orderedMonoid = record
    { poset = poset ; _∙_ = _∙_ ; ε = ε ; isMonoid = IsCommutativeMonoid.isMonoid isCommutativeMonoid ; ∙-mono = ∙-mono }
