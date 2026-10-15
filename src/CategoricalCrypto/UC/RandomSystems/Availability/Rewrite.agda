{-# OPTIONS --safe --without-K --guardedness #-}

-- rewrite⇒RS is identity on objects and cap maps. Its computation image
-- inserts an identity; the measured transport cancels it without error.
-- Keep the second generic setup instance out of the native QRS bridge.

open import Categories.Category.Monoidal.Bundle

open import Data.Rational using (ℚ)
open import Function.Bundles

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.UC.Model.Quantitative using (QSetupᵒ)
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.RandomSystems.Availability
open import CategoricalCrypto.UC.RandomSystems.Quantitative

import CategoricalCrypto.UC.Model.Setup as Sᵒ
import CategoricalCrypto.UC.Quantitative.Availability as Designated

module CategoricalCrypto.UC.RandomSystems.Availability.Rewrite where

module QAvailabilityᵒ = Designated.Designated ℚ-ordered QSetupᵒ

private
  module G = MonoidalCategory 𝔾ᵒ
  variable
    A B X Y : G.Obj
    εₛ εₐ : ℚ

rewrite-availability : {a : X G.⇒ G.unit} {b : Y G.⇒ G.unit}
                       {f : A G.⇒ Sᵒ.T₀ X B} {g : A G.⇒ Sᵒ.T₀ Y B}
                     → QAvailabilityᵒ.Availability εₐ a b f g
                     → QAvailabilityᴿ.Availability εₐ a b f g
rewrite-availability {εₐ = ε} {a = a} {b} {f} {g} e =
  Equivalence.to (≈ᵁᴿ[]-G⇔ {ε = ε} {f = Sᵒ.sub a G.∘ f} {g = Sᵒ.sub b G.∘ g})
    (≈ᵁ[]⇒≈ᵁᴿ[] {ε = ε} {f = Sᵒ.sub a G.∘ f} {g = Sᵒ.sub b G.∘ g} e)

rewrite-secure-available : {a : X G.⇒ G.unit} {b : Y G.⇒ G.unit}
                           {f : A G.⇒ Sᵒ.T₀ X B} {g : A G.⇒ Sᵒ.T₀ Y B}
                         → QAvailabilityᵒ.SecureAvailable εₛ εₐ a b f g
                         → QAvailabilityᴿ.SecureAvailable εₛ εₐ a b f g
rewrite-secure-available {εₛ = εs} {εₐ = εa} {a = a} {b} {f} {g} c =
  QAvailabilityᴿ.secure-available
    (Equivalence.to (≤UCᴿ[]-G⇔ {ε = εs} {f = f} {g = g})
      (Witness⇒≤UCᴿ[] {ε = εs} {f = f} {g = g} (QAvailabilityᵒ.SecureAvailable.security c)))
    (rewrite-availability {εₐ = εa} {a = a} {b} {f} {g}
      (QAvailabilityᵒ.SecureAvailable.availability c))
