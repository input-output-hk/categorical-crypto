{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Category (Sort : Set) (Payload : Sort → Set) where

open import Categories.Category.Core
open import Categories.Category.Helper
open import Level using (0ℓ; suc)
open import Relation.Binary using (IsEquivalence)

open import CategoricalCrypto.CSP.Associativity Sort Payload
open import CategoricalCrypto.CSP.Congruence Sort Payload
open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Plugging Sort Payload
open import CategoricalCrypto.CSP.Structure Sort Payload
open import CategoricalCrypto.CSP.Units Sort Payload

-- Opaque law witnesses prevent bundle conversion from expanding graph maps.
-- Objects, arrows, identity and composition remain definitionally available.
private
  variable
    A B C D : Interface
    f g h i : Network A B

  opaque
    associativity : {f : Network A B} {g : Network B C} {h : Network C D} →
      ((h ∘ g) ∘ f) ≅ (h ∘ (g ∘ f))
    associativity {f = f} {g} {h} = ≅-sym (Flatten.associative-plugging f g h)

    identityˡ : (id ∘ f) ≅ f
    identityˡ = RightUnit.identity-plugging _

    identityʳ : (f ∘ id) ≅ f
    identityʳ = LeftUnit.identity-plugging _

    equivalence : IsEquivalence (_≅_ {A} {B})
    equivalence = record { refl = ≅-refl ; sym = ≅-sym ; trans = ≅-trans }

    composition-congruence : {f h : Network B C} {g i : Network A B} →
      f ≅ h → g ≅ i → (f ∘ g) ≅ (h ∘ i)
    composition-congruence f g = PlugIso.plugging-congruence g f

OpenCSP : Category 0ℓ (suc 0ℓ) (suc 0ℓ)
OpenCSP = categoryHelper record
  { Obj = Interface ; _⇒_ = Network ; _≈_ = _≅_
  ; id = id ; _∘_ = _∘_
  ; assoc = associativity
  ; identityˡ = identityˡ ; identityʳ = identityʳ
  ; equiv = equivalence ; ∘-resp-≈ = composition-congruence }
