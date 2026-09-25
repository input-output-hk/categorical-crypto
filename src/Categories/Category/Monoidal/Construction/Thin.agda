{-# OPTIONS --safe --without-K #-}

-- The thin category of an ordered monoid is monoidal, with the monoid
-- operation as tensor and symmetric when the monoid is commutative.

module Categories.Category.Monoidal.Construction.Thin where

open import Algebra.Ordered.Bundles
open import Algebra.Structures
open import Data.Product
open import Relation.Binary using (Poset)

import Categories.Category.Construction.Thin as Thin
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Core
open import Categories.Category.Monoidal.Symmetric

module _ {c ℓ₁ ℓ₂} e (M : OrderedMonoid c ℓ₁ ℓ₂) where
  open OrderedMonoid M
  open Thin e poset
  open EqIsIso
  open IsMonoid isMonoid

  Thin-Monoidal : Monoidal Thin
  Thin-Monoidal = monoidalHelper Thin record
    { ⊗          = record { F₀ = uncurry _∙_ ; F₁ = uncurry ∙-mono }
    ; unit       = ε
    ; unitorˡ    = ≈⇒≅ (identityˡ _)
    ; unitorʳ    = ≈⇒≅ (identityʳ _)
    ; associator = ≈⇒≅ (assoc _ _ _)
    }

module _ {c ℓ₁ ℓ₂} e (M : OrderedCommutativeMonoid c ℓ₁ ℓ₂) where
  open OrderedCommutativeMonoid M
  open Poset poset
  open IsCommutativeMonoid isCommutativeMonoid using (comm)

  Thin-Symmetric : Symmetric (Thin-Monoidal e orderedMonoid)
  Thin-Symmetric = symmetricHelper _ record
    { braiding = record
      { F⇒G = record { η = λ (x , y) → reflexive (comm x y) }
      ; F⇐G = record { η = λ (x , y) → reflexive (comm y x) }
      }
    }

  Thin-SymmetricMonoidalCategory : SymmetricMonoidalCategory c ℓ₂ e
  Thin-SymmetricMonoidalCategory = record { symmetric = Thin-Symmetric }
