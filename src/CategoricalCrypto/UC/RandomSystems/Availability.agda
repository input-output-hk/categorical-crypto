{-# OPTIONS --safe --without-K --guardedness #-}

-- Maurer 2011 §5.1 Definition 3, with the honest protocol already included
-- in f = πR. The grade is Eve's interface; a designated converter X ⇒ I
-- shields it, possibly answering internal mode queries. The honest boundary
-- A ⇒ B is unchanged. These converters are parameters, not simulators chosen
-- after a test. Equal errors and a shared designated converter specialize to
-- Definition 3; distinct typed converters retain resource-specific modes. See
-- docs/uc-setup-random-systems.md §4.5 for the model assumptions.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient

open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties
open import Function.Bundles
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.RandomSystems.Advantage
open import CategoricalCrypto.UC.RandomSystems.Composition
open import CategoricalCrypto.UC.RandomSystems.Construction
open import CategoricalCrypto.UC.RandomSystems.Seal
open import CategoricalCrypto.UC.RandomSystems.Quantitative

import CategoricalCrypto.UC.Model.Setup as Sᵒ
import CategoricalCrypto.UC.Quantitative.Availability as Designated

module CategoricalCrypto.UC.RandomSystems.Availability where

module QAvailabilityᴿ = Designated.Designated ℚ-ordered QSetupᴿ

private
  module G = MonoidalCategory 𝔾ᵒ
  module Q = MonoidalCongruence congᴿ
  variable
    A B : G.Obj
    X Y Z : G.Obj
    εₛ εₐ εₛ′ εₐ′ : ℚ

no-adversary : X G.⇒ G.unit → A G.⇒ Sᵒ.T₀ X B → A G.⇒ B
no-adversary a f = G.unitorˡ.from G.∘ (Sᵒ.sub a G.∘ f)

Available : X G.⇒ G.unit → Y G.⇒ G.unit
          → A G.⇒ Sᵒ.T₀ X B → A G.⇒ Sᵒ.T₀ Y B → Set
Available a b f g = no-adversary a f Q.∼ no-adversary b g

AvailableWithin : ℚ → X G.⇒ G.unit → Y G.⇒ G.unit
                → A G.⇒ Sᵒ.T₀ X B → A G.⇒ Sᵒ.T₀ Y B → Set
AvailableWithin ε a b f g = no-adversary a f ∼ᴿ[ ε ] no-adversary b g

Available⇔AvailableWithin₀ : {a : X G.⇒ G.unit} {b : Y G.⇒ G.unit}
                            {f : A G.⇒ Sᵒ.T₀ X B} {g : A G.⇒ Sᵒ.T₀ Y B}
                          → Available a b f g ⇔ AvailableWithin 0ℚ a b f g
Available⇔AvailableWithin₀ {a = a} {b} {f} {g} =
  ∼ᴿ⇔∼ᴿ[0] {f = no-adversary a f} {g = no-adversary b g}

record SecureConstruction (a : X G.⇒ G.unit) (b : Y G.⇒ G.unit)
                          (f : A G.⇒ Sᵒ.T₀ X B) (g : A G.⇒ Sᵒ.T₀ Y B) : Set₁ where
  constructor secure-construction
  field security : f Sᵒ.≤UC g
        availability : Available a b f g

record SecurelyConstructs (εₛ εₐ : ℚ) (a : X G.⇒ G.unit) (b : Y G.⇒ G.unit)
                          (f : A G.⇒ Sᵒ.T₀ X B) (g : A G.⇒ Sᵒ.T₀ Y B) : Set₁ where
  constructor securely-constructs
  field security : Constructs εₛ f g
        availability : AvailableWithin εₐ a b f g

SecureConstruction⇔SecurelyConstructs₀ : {a : X G.⇒ G.unit} {b : Y G.⇒ G.unit}
                                        {f : A G.⇒ Sᵒ.T₀ X B} {g : A G.⇒ Sᵒ.T₀ Y B}
                                      → SecureConstruction a b f g ⇔ SecurelyConstructs 0ℚ 0ℚ a b f g
SecureConstruction⇔SecurelyConstructs₀ {a = a} {b} {f} {g} = mk⇔
  (λ c → securely-constructs (≤UC⇒Constructs₀ {f = f} {g = g} (SecureConstruction.security c))
           (Equivalence.to (Available⇔AvailableWithin₀ {a = a} {b = b} {f = f} {g = g})
                           (SecureConstruction.availability c)))
  (λ c → secure-construction (Constructs₀⇒≤UC {f = f} {g = g} (SecurelyConstructs.security c))
           (Equivalence.from (Available⇔AvailableWithin₀ {a = a} {b = b} {f = f} {g = g})
                             (SecurelyConstructs.availability c)))

------------------------------------------------------------------------
-- The native and generic designated comparisons
------------------------------------------------------------------------

private
  post-within : {C : G.Obj} (u : B G.⇒ C) {f g : A G.⇒ B}
              → f ∼ᴿ[ εₐ ] g → (u G.∘ f) ∼ᴿ[ εₐ ] (u G.∘ g)
  post-within {εₐ = ε} u {f} {g} e =
    ≈ᴿ[]-mono (≤-reflexive (+-identityˡ ε))
      (∘-resp-∼ᴿ[] {f = u} {h = u} {g = f} {i = g} (≈⇒∼ᴿ[0] G.Equiv.refl) e)

  unitor-cancel : (f : A G.⇒ Sᵒ.T₀ G.unit B)
                → (G.unitorˡ.to G.∘ (G.unitorˡ.from G.∘ f)) G.≈ f
  unitor-cancel f = G.Equiv.trans G.sym-assoc
    (G.Equiv.trans (G.∘-resp-≈ˡ G.unitorˡ.isoˡ) G.identityˡ)

Availability⇔AvailableWithin : {a : X G.⇒ G.unit} {b : Y G.⇒ G.unit}
                               {f : A G.⇒ Sᵒ.T₀ X B} {g : A G.⇒ Sᵒ.T₀ Y B}
                             → QAvailabilityᴿ.Availability εₐ a b f g ⇔ AvailableWithin εₐ a b f g
Availability⇔AvailableWithin {εₐ = ε} {a = a} {b} {f} {g} = mk⇔
  (λ e → post-within G.unitorˡ.from
    (≈ᵁᴿ[]⇒∼ᴿ[] {ε = ε} {f = Sᵒ.sub a G.∘ f} {g = Sᵒ.sub b G.∘ g} e))
  (λ e → QUCᴿ.ctx-resp (Q.≈⇒∼ (unitor-cancel (Sᵒ.sub a G.∘ f)))
    (Q.≈⇒∼ (unitor-cancel (Sᵒ.sub b G.∘ g)))
    (∼ᴿ[]⇒≈ᵁᴿ[] {ε = ε}
      {f = G.unitorˡ.to G.∘ no-adversary a f} {g = G.unitorˡ.to G.∘ no-adversary b g}
      (post-within G.unitorˡ.to e)))

SecureAvailable⇔SecurelyConstructs : {a : X G.⇒ G.unit} {b : Y G.⇒ G.unit}
                                      {f : A G.⇒ Sᵒ.T₀ X B} {g : A G.⇒ Sᵒ.T₀ Y B}
                                    → QAvailabilityᴿ.SecureAvailable εₛ εₐ a b f g
                                    ⇔ SecurelyConstructs εₛ εₐ a b f g
SecureAvailable⇔SecurelyConstructs {εₛ = εs} {εₐ = εa} {a = a} {b} {f} {g} = mk⇔
  (λ c → securely-constructs
    (≤UCᴿ[]⇒Constructs {ε = εs} {f = f} {g = g} (QAvailabilityᴿ.SecureAvailable.security c))
    (Equivalence.to (Availability⇔AvailableWithin {εₐ = εa} {a = a} {b} {f} {g})
      (QAvailabilityᴿ.SecureAvailable.availability c)))
  (λ c → QAvailabilityᴿ.secure-available
    (Constructs⇒≤UCᴿ[] {ε = εs} {f = f} {g = g} (SecurelyConstructs.security c))
    (Equivalence.from (Availability⇔AvailableWithin {εₐ = εa} {a = a} {b} {f} {g})
      (SecurelyConstructs.availability c)))

SecureConstruction⇔SecureAvailable₀ : {a : X G.⇒ G.unit} {b : Y G.⇒ G.unit}
                                       {f : A G.⇒ Sᵒ.T₀ X B} {g : A G.⇒ Sᵒ.T₀ Y B}
                                     → SecureConstruction a b f g
                                     ⇔ QAvailabilityᴿ.SecureAvailable 0ℚ 0ℚ a b f g
SecureConstruction⇔SecureAvailable₀ {a = a} {b} {f} {g} = mk⇔
  (λ c → Equivalence.from (SecureAvailable⇔SecurelyConstructs {a = a} {b} {f} {g})
    (Equivalence.to (SecureConstruction⇔SecurelyConstructs₀ {a = a} {b} {f} {g}) c))
  (λ c → Equivalence.from (SecureConstruction⇔SecurelyConstructs₀ {a = a} {b} {f} {g})
    (Equivalence.to (SecureAvailable⇔SecurelyConstructs {a = a} {b} {f} {g}) c))

------------------------------------------------------------------------
-- Converter compatibility
------------------------------------------------------------------------

no-adversary-resp-converter : {a b : X G.⇒ G.unit} (f : A G.⇒ Sᵒ.T₀ X B)
                            → a Q.∼ b → no-adversary a f Q.∼ no-adversary b f
no-adversary-resp-converter f e =
  Q.∘-resp-∼ Q.∼.refl (Q.∘-resp-∼ (Q.⊗-resp-∼ e Q.∼.refl) Q.∼.refl)

no-adversary-regrade : (a : X G.⇒ G.unit) (s : Y G.⇒ X) (g : A G.⇒ Sᵒ.T₀ Y B)
                    → no-adversary a (Sᵒ.sub s G.∘ g) G.≈ no-adversary (a G.∘ s) g
no-adversary-regrade a s g = G.∘-resp-≈ʳ
  (G.Equiv.trans G.sym-assoc (G.∘-resp-≈ˡ (G.Equiv.sym Sᵒ.sub-homomorphism)))

-- A simulator factoring is sufficient for full construction only when its
-- composition with the real no-adversary converter preserves the ideal mode.
secure-construction-factor : {a : X G.⇒ G.unit} {b : Y G.⇒ G.unit}
                             {s : Y G.⇒ X} {f : A G.⇒ Sᵒ.T₀ X B} {g : A G.⇒ Sᵒ.T₀ Y B}
                           → f G.≈ (Sᵒ.sub s G.∘ g) → (a G.∘ s) Q.∼ b
                           → SecureConstruction a b f g
secure-construction-factor {a = a} {b} {s} {f} {g} factor compat =
  Equivalence.from (SecureConstruction⇔SecureAvailable₀ {a = a} {b} {f} {g})
    (QAvailabilityᴿ.secure-mode-preserving {s = s} {f = f} {g = g} compat
      (∼ᴿ[]⇒≈ᵁᴿ[] {ε = 0ℚ} {f = f} {g = Sᵒ.sub s G.∘ g}
        (≈⇒∼ᴿ[0] {f = f} {g = Sᵒ.sub s G.∘ g} factor)))

------------------------------------------------------------------------
-- Replacement composition
------------------------------------------------------------------------

-- The middle resource must have compatible designated no-adversary modes;
-- security-only transitivity supplies no such compatibility.
secure-construction-trans : {a : X G.⇒ G.unit} {b b′ : Y G.⇒ G.unit} {c : Z G.⇒ G.unit}
                            {f : A G.⇒ Sᵒ.T₀ X B} {g : A G.⇒ Sᵒ.T₀ Y B} {h : A G.⇒ Sᵒ.T₀ Z B}
                          → b Q.∼ b′ → SecureConstruction a b f g → SecureConstruction b′ c g h
                          → SecureConstruction a c f h
secure-construction-trans {a = a} {b} {b′} {c} {f} {g} {h} compat cf cg =
  Equivalence.from (SecureConstruction⇔SecureAvailable₀ {a = a} {b = c} {f = f} {g = h})
    (QAvailabilityᴿ.secure-trans-cap {f = f} {g = g} {h = h} compat
      (Equivalence.to (SecureConstruction⇔SecureAvailable₀ {a = a} {b} {f} {g}) cf)
      (Equivalence.to (SecureConstruction⇔SecureAvailable₀ {a = b′} {b = c} {f = g} {g = h}) cg))

securely-constructs-trans : {a : X G.⇒ G.unit} {b b′ : Y G.⇒ G.unit} {c : Z G.⇒ G.unit}
                            {f : A G.⇒ Sᵒ.T₀ X B} {g : A G.⇒ Sᵒ.T₀ Y B} {h : A G.⇒ Sᵒ.T₀ Z B}
                          → b Q.∼ b′ → SecurelyConstructs εₛ εₐ a b f g
                          → SecurelyConstructs εₛ′ εₐ′ b′ c g h
                          → SecurelyConstructs (εₛ ℚ.+ εₛ′) (εₐ ℚ.+ εₐ′) a c f h
securely-constructs-trans {εₛ = εₛ} {εₐ} {εₛ′} {εₐ′} {a} {b} {b′} {c} {f} {g} {h} compat cf cg =
  Equivalence.to (SecureAvailable⇔SecurelyConstructs {a = a} {b = c} {f = f} {g = h})
    (QAvailabilityᴿ.secure-trans-cap {f = f} {g = g} {h = h} compat
      (Equivalence.from (SecureAvailable⇔SecurelyConstructs {a = a} {b} {f} {g}) cf)
      (Equivalence.from (SecureAvailable⇔SecurelyConstructs {a = b′} {b = c} {f = g} {g = h}) cg))
