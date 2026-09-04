{-# OPTIONS --safe --without-K #-}

-- The machine layer as a symmetric monoidal category.  Two shapes are worth
-- noting: the tensor's unit is the base's `⊥`, not `unit`, because `_⊗ᵉ_` pairs
-- interfaces by the *coproduct*; and the helper records are the shorter ones —
-- `monoidalHelper` derives the `⇐` halves of the unitor and associator squares
-- by conjugation and `symmetricHelper` the second hexagon from the first, so
-- `Tensor.Structural` proves each law only once.

open import Categories.Category.Monoidal using (Monoidal; monoidalHelper)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Pure using (PureSub)
open import Categories.Category.Monoidal.Symmetric using (Symmetric; symmetricHelper)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
import Categories.Category.Monoidal.Distributive as MD

open import Data.Product using (_,_)
open import Level using (_⊔_)

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
open Sim 𝒱 𝒫
open Structural 𝒱 dist 𝒫
open Tensor 𝒱 dist 𝒫

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
  ; unitorˡ         = record { from = λ⇒ᴹ ; to = λ⇐ᴹ
                             ; iso = record { isoˡ = ≲⇒≈ᴹ λᴹ-isoˡ
                                            ; isoʳ = ≲⇒≈ᴹ λᴹ-isoʳ } }
  ; unitorʳ         = record { from = ρ⇒ᴹ ; to = ρ⇐ᴹ
                             ; iso = record { isoˡ = ≲⇒≈ᴹ ρᴹ-isoˡ
                                            ; isoʳ = ≲⇒≈ᴹ ρᴹ-isoʳ } }
  ; associator      = record { from = α⇒ᴹ ; to = α⇐ᴹ
                             ; iso = record { isoˡ = ≲⇒≈ᴹ αᴹ-isoˡ
                                            ; isoʳ = ≲⇒≈ᴹ αᴹ-isoʳ } }
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
