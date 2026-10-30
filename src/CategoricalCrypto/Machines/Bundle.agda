{-# OPTIONS --safe --without-K #-}

-- Interfaces use the base's coproduct tensor and initial object, not its
-- state tensor. Naturality for arbitrary machines is the extra input to
-- transporting the coproduct coherence along `pureF`.

open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Construction.Transport as Transport
import Categories.Category.Monoidal.Construction.Transport.Symmetric as TransportSymmetric
open import Categories.Category.Monoidal.Subcategory
open import Categories.Category.Monoidal.Symmetric
open import Categories.Category.Unbundled.Properties
open import Categories.Functor.Bifunctor
open import Categories.Functor.Core
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Cocartesian.Monoidal as Cocart
import Categories.Category.Cocartesian.SymmetricMonoidal as CocartSym
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
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : WideSymmetricMonoidalSubcategory 𝒱) where

open Assoc 𝒱 dist 𝒫
open MCat 𝒱 𝒫
open MD.MonoidalDistributive dist
open CE (SymmetricMonoidalCategory.U 𝒱) cocartesian
open Sim 𝒱 𝒫
open Structural 𝒱 dist 𝒫
open Tensor 𝒱 dist 𝒫

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

private
  module ⊕Monoidal = Cocart.CocartesianMonoidal cocartesian
  module ⊕Symmetric = CocartSym.CocartesianSymmetricMonoidal
                       (SymmetricMonoidalCategory.U 𝒱) cocartesian

  module T = Transport
    (unpack′ (SymmetricMonoidalCategory.U 𝒱)) (unpack′ Mealy-Category)
    ⊕Monoidal.+-monoidal (record { Functor pureF })

  transport : T.Transport
  transport = record
    { _⊗₁_ = λ f g → Functor.F₁ ⊗ᴹ (f , g)
    ; ⊗-identity = Functor.identity ⊗ᴹ
    ; ⊗-homomorphism = Functor.homomorphism ⊗ᴹ
    ; ⊗-resp-≈ = λ eq₁ eq₂ → Functor.F-resp-≈ ⊗ᴹ (eq₁ , eq₂)
    ; ⊗-compatible = λ f g → ≲⇒≈ᴹ (⊗ᵉ-pureᴹ f g)
    ; unitorˡ-commute = unitorˡ-commuteᴹ
    ; unitorʳ-commute = unitorʳ-commuteᴹ
    ; assoc-commute = assoc-commuteᴹ
    }

  module S = TransportSymmetric
    {C = unpack′ (SymmetricMonoidalCategory.U 𝒱)} {D = unpack′ Mealy-Category}
    {M = ⊕Monoidal.+-monoidal} {F = record { Functor pureF }} transport ⊕Symmetric.+-symmetric

Mealy-Monoidal : Monoidal Mealy-Category
Mealy-Monoidal = T.Transport.monoidal transport

-- Fieldwise assembly avoids converting the entire transported monoidal index.
Mealy-Symmetric : Symmetric Mealy-Monoidal
Mealy-Symmetric = record
  { braided = record
      { braiding = S.braiding braiding-commuteᴹ
      ; hexagon₁ = S.hexagon₁
      ; hexagon₂ = S.hexagon₂ braiding-commuteᴹ
      }
  ; commutative = S.commutative
  }

Mealy-SymmetricMonoidal : SymmetricMonoidalCategory o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
Mealy-SymmetricMonoidal = record
  { U = Mealy-Category ; monoidal = Mealy-Monoidal ; symmetric = Mealy-Symmetric }
