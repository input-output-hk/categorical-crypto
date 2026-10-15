{-# OPTIONS --safe --without-K --guardedness #-}

-- Quotienting changes equality, not the braiding's processes or tensor order.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient
open import Categories.Category.Monoidal.Symmetric
open import Categories.NaturalTransformation.NaturalIsomorphism

open import CategoricalCrypto.UC.Model.Symmetric
open import CategoricalCrypto.UC.RandomSystems.Seal

import CategoricalCrypto.UC.RandomSystems.Setup as RS

module CategoricalCrypto.UC.RandomSystems.Availability.Symmetric where

private
  module S = Symmetric symmetricᵒ
  module Q = MonoidalCongruence congᴿ

symmetricᴿ : Symmetric (MonoidalCategory.monoidal RS.𝔾ᴿ)
symmetricᴿ = record
  { braided = record
    { braiding = niHelper record
      { η = S.braiding.⇒.η
      ; η⁻¹ = S.braiding.⇐.η
      ; commute = λ f → Q.≈⇒∼ (S.braiding.⇒.commute f)
      ; iso = λ X → record
        { isoˡ = Q.≈⇒∼ (S.braiding.iso.isoˡ X)
        ; isoʳ = Q.≈⇒∼ (S.braiding.iso.isoʳ X)
        }
      }
    ; hexagon₁ = Q.≈⇒∼ S.hexagon₁
    ; hexagon₂ = Q.≈⇒∼ S.hexagon₂
    }
  ; commutative = Q.≈⇒∼ S.commutative
  }
