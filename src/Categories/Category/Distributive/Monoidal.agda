{-# OPTIONS --safe --without-K #-}

-- A distributive category is monoidal-distributive for its cartesian product: `-×-`'s
-- `F₁` is `_⁂_`, so the two `distributeˡ` are the same term.

open import Categories.Category.Cartesian.Monoidal
open import Categories.Category.Core
open import Categories.Category.Distributive
open import Categories.Category.Monoidal.Bundle
import Categories.Category.Cartesian.SymmetricMonoidal as CartesianSymmetric
import Categories.Category.Monoidal.Distributive as MD

module Categories.Category.Distributive.Monoidal {o ℓ e} {𝒞 : Category o ℓ e} (D : Distributive 𝒞) where

open Distributive D

Cartesian-SymmetricMonoidal : SymmetricMonoidalCategory o ℓ e
Cartesian-SymmetricMonoidal = record
  { U         = 𝒞
  ; monoidal  = CartesianMonoidal.monoidal cartesian
  ; symmetric = CartesianSymmetric.symmetric 𝒞 cartesian
  }

MonoidalDistributive-Cartesian : MD.MonoidalDistributive Cartesian-SymmetricMonoidal
MonoidalDistributive-Cartesian = record { cocartesian = cocartesian ; isIsoˡ = isIsoˡ }
