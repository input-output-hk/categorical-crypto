{-# OPTIONS --safe --without-K #-}

-- The machine layer as a symmetric monoidal category.  Two shapes are worth
-- noting: the tensor's unit is the base's `⊥`, not `unit`, because `_⊗ᵉ_` pairs
-- interfaces by the *coproduct*; and the helper records are the shorter ones —
-- `monoidalHelper` derives the `⇐` halves of the unitor and associator squares
-- by conjugation and `symmetricHelper` the second hexagon from the first, so
-- `Tensor.Structural` proves each law only once.

open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor.Bifunctor
open import Categories.Functor.Core
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Categories.NaturalTransformation.NaturalIsomorphism
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.Distributive as MD

open import Data.Product
open import Level

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Tensor.Assoc as Assoc
import CategoricalCrypto.Machines.Tensor.Structural as Structural

module CategoricalCrypto.Machines.Bundle
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱) where

open Assoc 𝒱 dist 𝒫
open MCat 𝒱 𝒫
open MD.MonoidalDistributive dist
open CE (SymmetricMonoidalCategory.U 𝒱) cocartesian
open Sim 𝒱 𝒫
open Structural 𝒱 dist 𝒫
open Tensor 𝒱 dist 𝒫

-- A base map is a machine, functorially; so are its isomorphisms.
pureF : Functor (SymmetricMonoidalCategory.U 𝒱) Mealy-Category
pureF = record
  { F₀ = λ A → A ; F₁ = pureᴹ ; identity = ≲⇒≈ᴹ pureᴹ-id
  ; homomorphism = ≲⇒≈ᴹ˘ (pureᴹ-∘ _ _) ; F-resp-≈ = λ e → ≲⇒≈ᴹ (pureᴹ-cong e) }

⊗ᴹ : Bifunctor Mealy-Category Mealy-Category Mealy-Category
⊗ᴹ = record
  { F₀           = λ (A , B) → A + B
  ; F₁           = λ (f , g) → f ⊗ᵉ g
  ; identity     = ≲⇒≈ᴹ ⊗ᵉ-identity
  ; homomorphism = ⊗ᵉ-homomorphism
  ; F-resp-≈     = λ (e₁ , e₂) → ⊗ᵉ-resp-≈ᴹ e₁ e₂
  }

Mealy-Monoidal : Monoidal Mealy-Category
Mealy-Monoidal = monoidalHelper Mealy-Category record
  { ⊗               = ⊗ᴹ
  ; unit            = ⊥
  ; unitorˡ         = [ pureF ]-resp-≅ ⊕.unitorˡ
  ; unitorʳ         = [ pureF ]-resp-≅ ⊕.unitorʳ
  ; associator      = [ pureF ]-resp-≅ ⊕.associator
  ; unitorˡ-commute = unitorˡ-commuteᴹ
  ; unitorʳ-commute = unitorʳ-commuteᴹ
  ; assoc-commute   = assoc-commuteᴹ
  ; triangle        = triangleᴹ
  ; pentagon        = pentagonᴹ
  }

Mealy-Symmetric : Symmetric Mealy-Monoidal
Mealy-Symmetric = symmetricHelper Mealy-Monoidal record
  { braiding    = niHelper record
      { η       = λ _ → σᴹ
      ; η⁻¹     = λ _ → σᴹ
      ; commute = λ _ → braiding-commuteᴹ
      ; iso     = λ _ → record { isoˡ = ≲⇒≈ᴹ σᴹ-involutive
                               ; isoʳ = ≲⇒≈ᴹ σᴹ-involutive }
      }
  ; commutative = ≲⇒≈ᴹ σᴹ-involutive
  ; hexagon     = hexagonᴹ
  }

Mealy-SymmetricMonoidal : SymmetricMonoidalCategory o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
Mealy-SymmetricMonoidal = record
  { U = Mealy-Category ; monoidal = Mealy-Monoidal ; symmetric = Mealy-Symmetric }
