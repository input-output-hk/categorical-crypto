{-# OPTIONS --safe --without-K --guardedness #-}

-- Product caps close honest composition in protocol order. Native behavioral
-- bounds and generic UC bounds coincide at each supplied cap.

open import Categories.Category.Monoidal.Bundle

open import Data.Rational as ℚ using (ℚ)
open import Function.Bundles

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Symmetric
open import CategoricalCrypto.UC.RandomSystems.Availability
open import CategoricalCrypto.UC.RandomSystems.Quantitative

import CategoricalCrypto.UC.Model.Setup as PM
import CategoricalCrypto.UC.Quantitative.Availability.Composition as Composition
import CategoricalCrypto.UC.Quantitative.Availability.Standard as Standard

module CategoricalCrypto.UC.RandomSystems.Availability.Composition where

module QCompositionᴿ = Composition.Serial ℚ-ordered QSetupᴿ

private
  module G = MonoidalCategory 𝔾ᵒ
  module W = Standard.Structural ℚ-ordered 𝔾ᵒ symmetricᵒ
  variable
    A B C X Y P R : G.Obj
    εf εu εfs εfa εus εua : ℚ

cap-compose : X G.⇒ G.unit → P G.⇒ G.unit → (X G.⊗₀ P) G.⇒ G.unit
cap-compose a c = G.unitorˡ.from G.∘ (a G.⊗₁ c)

no-adversary-compose : (a : X G.⇒ G.unit) (c : P G.⇒ G.unit)
                       (f : A G.⇒ PM.T₀ X B) (u : B G.⇒ PM.T₀ P C)
                     → no-adversary (cap-compose a c) (u PM.∙ f)
                       G.≈ no-adversary c u G.∘ no-adversary a f
no-adversary-compose a c f u = G.Equiv.trans
  (G.∘-resp-≈ʳ (W.close-compose a c f u))
  (W.unit-close-compose ((PM.sub a) G.∘ f) ((PM.sub c) G.∘ u))

available-within-compose : {a : X G.⇒ G.unit} {b : Y G.⇒ G.unit}
                           {c : P G.⇒ G.unit} {d : R G.⇒ G.unit}
                           {f : A G.⇒ PM.T₀ X B} {g : A G.⇒ PM.T₀ Y B}
                           {u : B G.⇒ PM.T₀ P C} {v : B G.⇒ PM.T₀ R C}
                         → AvailableWithin εf a b f g → AvailableWithin εu c d u v
                         → AvailableWithin (εu ℚ.+ εf) (cap-compose a c) (cap-compose b d)
                             (u PM.∙ f) (v PM.∙ g)
available-within-compose {a = a} {b} {c} {d} {f} {g} {u} {v} hf hu =
  Equivalence.to (Availability⇔AvailableWithin {a = cap-compose a c} {b = cap-compose b d}
    {f = u PM.∙ f} {g = v PM.∙ g})
    (QCompositionᴿ.availability-compose {f = f} {g = g} {u = u} {v = v}
      (Equivalence.from (Availability⇔AvailableWithin {f = f} {g = g}) hf)
      (Equivalence.from (Availability⇔AvailableWithin {f = u} {g = v}) hu))

securely-constructs-compose : {a : X G.⇒ G.unit} {b : Y G.⇒ G.unit}
                              {c : P G.⇒ G.unit} {d : R G.⇒ G.unit}
                              {f : A G.⇒ PM.T₀ X B} {g : A G.⇒ PM.T₀ Y B}
                              {u : B G.⇒ PM.T₀ P C} {v : B G.⇒ PM.T₀ R C}
                            → SecurelyConstructs εfs εfa a b f g → SecurelyConstructs εus εua c d u v
                            → SecurelyConstructs (εus ℚ.+ εfs) (εua ℚ.+ εfa)
                                (cap-compose a c) (cap-compose b d) (u PM.∙ f) (v PM.∙ g)
securely-constructs-compose {a = a} {b} {c} {d} {f} {g} {u} {v} hf hu =
  Equivalence.to (SecureAvailable⇔SecurelyConstructs {a = cap-compose a c} {b = cap-compose b d}
    {f = u PM.∙ f} {g = v PM.∙ g})
    (QCompositionᴿ.secure-compose {f = f} {g = g} {u = u} {v = v}
      (Equivalence.from (SecureAvailable⇔SecurelyConstructs {f = f} {g = g}) hf)
      (Equivalence.from (SecureAvailable⇔SecurelyConstructs {f = u} {g = v}) hu))
