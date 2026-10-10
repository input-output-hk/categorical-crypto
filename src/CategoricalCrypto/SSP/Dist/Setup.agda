{-# OPTIONS --safe --without-K #-}

-- The SSP setup up to `≈ᵈ` (`docs/uc-setup-ssp-dist.md` §4): `Protᴹ`
-- quotiented by `congᵈ`, `ℰᵖ` descended to it, and the identity on protocols
-- and tests as a morphism out of `SSP.Setup`.

module CategoricalCrypto.SSP.Dist.Setup where

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient
open import Categories.Functor.Presheaf
open import Level

open import CategoricalCrypto.SSP.Dist
open import CategoricalCrypto.SSP.Protocol.Monoidal
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.UCSetup.Morphism

import CategoricalCrypto.SSP.Setup as SSP
import CategoricalCrypto.Standard2 as Std2

Protᵈ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
Protᵈ = quotient Protᴹ congᵈ

ℰᵈ : Presheaf (MonoidalCategory.U Protᵈ) (Setoids (suc 0ℓ) (suc 0ℓ))
ℰᵈ = descend Protᴹ congᵈ SSP.ℰᵖ ≈ᵈ⇒≋

open Std2.StdUC Protᵈ ℰᵈ public

ssp⇒dist : UCSetupMorphism SSP.StdSetup StdSetup
ssp⇒dist = StdUCMorphism Protᴹ Protᵈ SSP.ℰᵖ ℰᵈ (quotientF Protᴹ congᵈ) (descendᵛ Protᴹ congᵈ SSP.ℰᵖ ≈ᵈ⇒≋)
