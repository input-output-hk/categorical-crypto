{-# OPTIONS --safe --without-K #-}

-- The SSP setup up to `≈ᵈ` (`docs/uc-setup-ssp-dist.md` §4): `Protᴹ`
-- quotiented by `congᵈ`, `ℰᵖ` descended to it, and the identity on protocols
-- and tests as a morphism out of `SSP.Setup`.

module CategoricalCrypto.SSP.Dist.Setup where

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient
open import Categories.Functor.Presheaf
import Categories.Morphism as Mor
open import Data.Product.Base
open import Level

open import CategoricalCrypto.Abstract2.Morphism
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

private variable A B X Y : SSP.Channel

------------------------------------------------------------------------
-- Security across the quotient
------------------------------------------------------------------------

preserves-≈ᵁ : Transfer.Preserves-≈ᵁ ssp⇒dist
preserves-≈ᵁ = surjective⇒preserves-≈ᵁ Protᴹ Protᵈ SSP.ℰᵖ ℰᵈ
  (quotientF Protᴹ congᵈ) (descendᵛ Protᴹ congᵈ SSP.ℰᵖ ≈ᵈ⇒≋)
  (λ A → A , Mor.≅.refl (MonoidalCategory.U Protᵈ))
  (Transfer.epi⇒preserves-≈ℰ ssp⇒dist (descendᵛ-epi Protᴹ congᵈ SSP.ℰᵖ ≈ᵈ⇒≋))

preserves-≤UC : Transfer.Preserves-≤UC ssp⇒dist
preserves-≤UC = Transfer.transfer⁺ ssp⇒dist preserves-≈ᵁ

-- `G` includes the comparison's structural identity before the protocol.
G≈id : (f : A SSP.⇒ SSP.T₀ X B) → Transfer.G ssp⇒dist f ≈ f
G≈id f = identityˡ

ssp≤⇒dist≤ : {f : A SSP.⇒ SSP.T₀ X B} {g : A SSP.⇒ SSP.T₀ Y B}
           → f SSP.≤UC g → f ≤UC g
ssp≤⇒dist≤ {f = f} {g} le = ≤UC-resp-≈ (G≈id f) (G≈id g) (preserves-≤UC le)

-- The quotient keeps every ancilla and prefix context, so Mono reflects
-- each component directly; the source's unknown GradeStable is not needed.
dist≈ᵁ⇒ssp≈ᵁ : {f g : A SSP.⇒ SSP.T₀ X B} → f ≈ᵁ g → f SSP.≈ᵁ g
dist≈ᵁ⇒ssp≈ᵁ e W =
  Transfer.mono⇒reflects-≈ℰ ssp⇒dist
    (λ {A} {x} {y} → descendᵛ-mono Protᴹ congᵈ SSP.ℰᵖ ≈ᵈ⇒≋ {A} {x} {y}) (e W)

dist≤⇒ssp≤ : {f : A SSP.⇒ SSP.T₀ X B} {g : A SSP.⇒ SSP.T₀ Y B}
           → f ≤UC g → f SSP.≤UC g
dist≤⇒ssp≤ le a = let s , e = le a in s , dist≈ᵁ⇒ssp≈ᵁ e

reflects-≤UC : Transfer.Reflects-≤UC ssp⇒dist
reflects-≤UC {f = f} {g} le = dist≤⇒ssp≤ (≤UC-resp-≈ (G≈id f) (G≈id g) le)
