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

open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.RandomSystems.Advantage
open import CategoricalCrypto.UC.RandomSystems.Composition
open import CategoricalCrypto.UC.RandomSystems.Construction
open import CategoricalCrypto.UC.RandomSystems.Seal

import CategoricalCrypto.UC.Model.Setup as Sᵒ

module CategoricalCrypto.UC.RandomSystems.Availability where

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
secure-construction-factor {a = a} {b} {s} {f} {g} factor compat = secure-construction
  (Constructs₀⇒≤UC {f = f} {g = g} (s , ≈⇒∼ᴿ[0] {f = f} {g = Sᵒ.sub s G.∘ g} factor))
  (Q.∼.trans (Q.≈⇒∼ (G.∘-resp-≈ʳ (G.∘-resp-≈ʳ factor)))
    (Q.∼.trans (Q.≈⇒∼ (no-adversary-regrade a s g)) (no-adversary-resp-converter g compat)))

------------------------------------------------------------------------
-- Replacement composition
------------------------------------------------------------------------

-- The middle resource must have compatible designated no-adversary modes;
-- security-only transitivity supplies no such compatibility.
secure-construction-trans : {a : X G.⇒ G.unit} {b b′ : Y G.⇒ G.unit} {c : Z G.⇒ G.unit}
                            {f : A G.⇒ Sᵒ.T₀ X B} {g : A G.⇒ Sᵒ.T₀ Y B} {h : A G.⇒ Sᵒ.T₀ Z B}
                          → b Q.∼ b′ → SecureConstruction a b f g → SecureConstruction b′ c g h
                          → SecureConstruction a c f h
secure-construction-trans {g = g} compat cf cg = secure-construction
  (Sᵒ.≤UC-trans (SecureConstruction.security cf) (SecureConstruction.security cg))
  (Q.∼.trans (SecureConstruction.availability cf)
    (Q.∼.trans (no-adversary-resp-converter g compat) (SecureConstruction.availability cg)))

securely-constructs-trans : {a : X G.⇒ G.unit} {b b′ : Y G.⇒ G.unit} {c : Z G.⇒ G.unit}
                            {f : A G.⇒ Sᵒ.T₀ X B} {g : A G.⇒ Sᵒ.T₀ Y B} {h : A G.⇒ Sᵒ.T₀ Z B}
                          → b Q.∼ b′ → SecurelyConstructs εₛ εₐ a b f g
                          → SecurelyConstructs εₛ′ εₐ′ b′ c g h
                          → SecurelyConstructs (εₛ ℚ.+ εₛ′) (εₐ ℚ.+ εₐ′) a c f h
securely-constructs-trans {εₛ = εₛ} {εₐ} {εₛ′} {εₐ′} {a} {b} {b′} {c} {f} {g} {h} compat cf cg =
  securely-constructs
    (constructs-trans {ε = εₛ} {ε′ = εₛ′} {f = f} {g = g} {h = h}
                      (SecurelyConstructs.security cf) (SecurelyConstructs.security cg))
    (≈ᴿ[]-mono (≤-reflexive (cong (εₐ ℚ.+_) (+-identityˡ εₐ′)))
      (≈ᴿ[]-trans (SecurelyConstructs.availability cf)
        (≈ᴿ[]-trans
          (Equivalence.to (∼ᴿ⇔∼ᴿ[0] {f = no-adversary b g} {g = no-adversary b′ g})
                          (no-adversary-resp-converter g compat))
          (SecurelyConstructs.availability cg))))
