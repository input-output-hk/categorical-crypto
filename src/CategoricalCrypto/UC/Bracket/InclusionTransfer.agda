{-# OPTIONS --safe --without-K --guardedness #-}

-- The source of `ι⇒prot` keeps all PM tests and closures.  Singleton channel
-- tags change only the presentation of an object, so every PM ancilla is an
-- inclusion image up to isomorphism.  See `docs/uc-setup-ssp.md` §6.

open import Categories.Category.Monoidal.Bundle
open import Categories.Functor.Monoidal
open import Categories.Functor.Properties
open import Categories.Morphism.Notation

open import Data.Product.Base
open import Data.Unit.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.UC.Bracket.Monoidal
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Wire.Algebra
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup using (ℰᵒ)

import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Bracket.InclusionTransfer where

private
  module G = MonoidalCategory 𝔾ᵒ
  module I = StrongMonoidalFunctor ιᴹ
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

opaque
  unfolding 𝔾ᵒ ifaceᵒ objᵒ

  oneᵒ : (X : G.Obj) → G.U [ I.₀ (oneᴵ (objᵒ X)) ≅ X ]
  oneᵒ X = record
    { from = wireᴹ proj₂ (tt ,_)
    ; to = wireᴹ (tt ,_) proj₂
    ; iso = record
      { isoˡ = wire∘wire (tt ,_) proj₂ proj₂ (tt ,_)
          S.○ᴹ wire-cong (λ { (tt , _) → refl }) (λ { (tt , _) → refl }) S.○ᴹ wire-id
      ; isoʳ = wire∘wire proj₂ (tt ,_) (tt ,_) proj₂
          S.○ᴹ wire-cong (λ _ → refl) (λ _ → refl) S.○ᴹ wire-id
      }
    }

ι-essentially-surjective : EssentiallySurjective I.F
ι-essentially-surjective X = oneᴵ (objᵒ X) , oneᵒ X

ι-preserves-≈ℰ : Transfer.Preserves-≈ℰ ι⇒prot
ι-preserves-≈ℰ = Transfer.epi⇒preserves-≈ℰ ι⇒prot (λ {A} → νι-epi {A})

ι-preserves-≈ᵁ : Transfer.Preserves-≈ᵁ ι⇒prot
ι-preserves-≈ᵁ = surjective⇒preserves-≈ᵁ 𝒲ᴹ 𝔾ᵒ ι*ℰᵒ ℰᵒ ιᴹ νι
  ι-essentially-surjective ι-preserves-≈ℰ

ι-preserves-≤UC : Transfer.Preserves-≤UC ι⇒prot
ι-preserves-≤UC = Transfer.transfer⁺ ι⇒prot ι-preserves-≈ᵁ
