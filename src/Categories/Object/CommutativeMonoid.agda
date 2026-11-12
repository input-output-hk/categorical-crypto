{-# OPTIONS --safe --without-K #-}

open import Categories.Category.Core
open import Categories.Category.Monoidal.Braided
open import Categories.Category.Monoidal.Core

module Categories.Object.CommutativeMonoid
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (B : Braided M) where

open import Categories.Category.Monoidal.Braided.Properties
open import Categories.Object.Monoid M
open import Level

open Category C
open Shorthands B

record IsCommutativeMonoid (E : Obj) : Set (ℓ ⊔ e) where
  field isMonoid : IsMonoid E

  open IsMonoid isMonoid public

  field commutative : μ ∘ σ⇒ ≈ μ

record CommutativeMonoid : Set (o ⊔ ℓ ⊔ e) where
  field
    Carrier : Obj
    isCommutativeMonoid : IsCommutativeMonoid Carrier

  open IsCommutativeMonoid isCommutativeMonoid public

  monoid : Monoid
  monoid = record { isMonoid = isMonoid }
