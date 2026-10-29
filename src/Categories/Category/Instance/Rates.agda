{-# OPTIONS --safe --without-K #-}

-- The positive naturals as a thin symmetric monoidal category.

module Categories.Category.Instance.Rates where

open import Data.Nat.Positive
open import Level

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Thin

Rates : SymmetricMonoidalCategory 0ℓ 0ℓ 0ℓ
Rates = Thin-SymmetricMonoidalCategory 0ℓ ·-1-OrderedCommutativeMonoid
