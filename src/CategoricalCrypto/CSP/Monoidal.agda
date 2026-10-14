{-# OPTIONS --safe --without-K --guardedness #-}

-- Coherence is equality of typed alias graphs, retaining every process box.
-- Structural arrows have empty box families; wire normalization uses connected
-- classes rather than adding a forwarding process or a silent transition.
-- Graph coherence proofs are imported opaquely; the bundle and wire maps reduce.
-- Standard2's tensor-grade action therefore needs no category transport.
module CategoricalCrypto.CSP.Monoidal (Sort : Set) (Payload : Sort → Set) where

open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Bundle
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MorphismReasoning
open import Data.Sum.Base using (inj₁; inj₂)
open import Level using (0ℓ; suc)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Category Sort Payload
open import CategoricalCrypto.CSP.FiniteWires Sort Payload
open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Plugging Sort Payload
open import CategoricalCrypto.CSP.Structure Sort Payload
open import CategoricalCrypto.CSP.Tensor Sort Payload
import CategoricalCrypto.CSP.TensorCoherence Sort Payload as TC
open TC public using (identity-wire-tensor; wire-identity-tensor; triangle; pentagon)
open import CategoricalCrypto.CSP.WireLaws Sort Payload

opaque
  wire-inverseˡ : ∀ {A B} (f : PortIso A B) → (wire (port-inverse f) ∘ wire f) ≅ id
  wire-inverseˡ {A} f = ≅-trans (Composition.compose-wires f (port-inverse f))
    (≅-trans (Extensional.wire-resp (port-compose (port-inverse f) f) (port-id A) (PortIso.left f)) (wire-id A))

  wire-inverseʳ : ∀ {A B} (f : PortIso A B) → (wire f ∘ wire (port-inverse f)) ≅ id
  wire-inverseʳ {B = B} f = ≅-trans (Composition.compose-wires (port-inverse f) f)
    (≅-trans (Extensional.wire-resp (port-compose f (port-inverse f)) (port-id B) (PortIso.right f)) (wire-id B))

wire-iso : ∀ {A B} → PortIso A B → Morphism._≅_ OpenCSP A B
wire-iso f = record
  { from = wire f ; to = wire (port-inverse f)
  ; iso = record { isoˡ = wire-inverseˡ f ; isoʳ = wire-inverseʳ f } }

private variable
  A B C D E F : Interface

opaque
  wire-square-sym : {N M : Network A B} → N ≅ M → M ≅ N
  wire-square-sym = ≅-sym

  inverse-wire-square : (a : PortIso A B) (b : PortIso C D)
    {f : Network B D} {g : Network A C} →
    (f ∘ wire a) ≅ (wire b ∘ g) →
    (wire (port-inverse b) ∘ f) ≅ (g ∘ wire (port-inverse a))
  inverse-wire-square a b {f} {g} = MorphismReasoning.conjugate-from OpenCSP
    (wire-iso a) (wire-iso b) {f = f} {g = g}

opaque
  left-unitor-to-natural : (f : Network A B) →
    (wire (port-inverse (left-unitor B)) ∘ f)
    ≅ ((id ⊗₁ f) ∘ wire (port-inverse (left-unitor A)))
  left-unitor-to-natural {A = A} {B = B} f = TC.LeftUnit.naturality-to {A = A} {B = B} f
    (Morphism._≅_.iso (wire-iso (left-unitor A))) (Morphism._≅_.iso (wire-iso (left-unitor B)))

  right-unitor-to-natural : (f : Network A B) →
    (wire (port-inverse (right-unitor B)) ∘ f)
    ≅ ((f ⊗₁ id) ∘ wire (port-inverse (right-unitor A)))
  right-unitor-to-natural {A = A} {B = B} f = TC.RightUnit.naturality-to {A = A} {B = B} f
    (Morphism._≅_.iso (wire-iso (right-unitor A))) (Morphism._≅_.iso (wire-iso (right-unitor B)))

  associator-to-natural : (f : Network A B) (g : Network C D) (h : Network E F) →
    (wire (port-inverse (associator B D F)) ∘ (f ⊗₁ (g ⊗₁ h)))
    ≅ (((f ⊗₁ g) ⊗₁ h) ∘ wire (port-inverse (associator A C E)))
  associator-to-natural {A = A} {B = B} {C = C} {D = D} {E = E} {F = F} f g h =
    TC.Associate.naturality-to {A = A} {B = B} {C = C} {D = D} {E = E} {F = F} f g h
      (Morphism._≅_.iso (wire-iso (associator A C E))) (Morphism._≅_.iso (wire-iso (associator B D F)))

OpenCSP-Monoidal : Monoidal OpenCSP
Monoidal.⊗ OpenCSP-Monoidal = tensor-bifunctor
Monoidal.unit OpenCSP-Monoidal = I
Monoidal.unitorˡ OpenCSP-Monoidal {X} = wire-iso (left-unitor X)
Monoidal.unitorʳ OpenCSP-Monoidal {X} = wire-iso (right-unitor X)
Monoidal.associator OpenCSP-Monoidal {X} {Y} {Z} = wire-iso (associator X Y Z)
Monoidal.unitorˡ-commute-from OpenCSP-Monoidal {A} {B} {f} = TC.LeftUnit.naturality {A = A} {B = B} f
Monoidal.unitorˡ-commute-to OpenCSP-Monoidal {A} {B} {f} = left-unitor-to-natural {A = A} {B = B} f
Monoidal.unitorʳ-commute-from OpenCSP-Monoidal {A} {B} {f} = TC.RightUnit.naturality {A = A} {B = B} f
Monoidal.unitorʳ-commute-to OpenCSP-Monoidal {A} {B} {f} = right-unitor-to-natural {A = A} {B = B} f
Monoidal.assoc-commute-from OpenCSP-Monoidal {A} {B} {f} {C} {D} {g} {E} {F} {h} =
  TC.Associate.naturality {A = A} {B = B} {C = C} {D = D} {E = E} {F = F} f g h
Monoidal.assoc-commute-to OpenCSP-Monoidal {A} {B} {f} {C} {D} {g} {E} {F} {h} =
  associator-to-natural {A = A} {B = B} {C = C} {D = D} {E = E} {F = F} f g h
Monoidal.triangle OpenCSP-Monoidal {X} {Y} = triangle X Y
Monoidal.pentagon OpenCSP-Monoidal {X} {Y} {Z} {W} = pentagon X Y Z W

OpenCSPᴹ : MonoidalCategory 0ℓ (suc 0ℓ) (suc 0ℓ)
OpenCSPᴹ = record { U = OpenCSP ; monoidal = OpenCSP-Monoidal }
