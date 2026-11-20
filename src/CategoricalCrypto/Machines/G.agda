{-# OPTIONS --safe --without-K #-}

-- The G construction over the traced machine category.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Subcategory
import Categories.Category.Monoidal.CoproductTrace as CT
import Categories.Category.Monoidal.Distributive as MD
open import Categories.GConstruction

open import Level

import CategoricalCrypto.Machines.Bundle as Bundle
import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Trace as Trace

module CategoricalCrypto.Machines.G {o ℓ e}
  (𝒱 : SymmetricMonoidalCategory o ℓ e) (dist : MD.MonoidalDistributive 𝒱)
  (𝒫 : WideSymmetricMonoidalSubcategory 𝒱) (E : CT.CoproductTrace 𝒱 dist 𝒫) where

open Bundle 𝒱 dist 𝒫
open MCat 𝒱 𝒫
open Trace 𝒱 dist 𝒫 E

Mealy-Gᴹ : MonoidalCategory o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
Mealy-Gᴹ = GConstructionMonoidalCategory Mealy-Category Mealy-Monoidal Mealy-Traced
