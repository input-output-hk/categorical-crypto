{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Tensor (Sort : Set) (Payload : Sort → Set) where

open import Categories.Functor.Bifunctor
open import Data.Product.Base using (uncurry)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Category Sort Payload
open import CategoricalCrypto.CSP.Congruence Sort Payload
open import CategoricalCrypto.CSP.FiniteWires Sort Payload
open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Interchange Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Plugging Sort Payload
open import CategoricalCrypto.CSP.Structure Sort Payload
open import CategoricalCrypto.CSP.WireLaws Sort Payload

opaque
  identity-tensor : ∀ {A B} → (id {A}) ⊗₁ (id {B}) ≅ id {A ⊗₀ B}
  identity-tensor {A} {B} = ≅-trans
    (TensorIso.tensor-congruence (≅-sym (wire-id A)) (≅-sym (wire-id B)))
    (≅-trans (TensorWires.tensor-wires (port-id A) (port-id B))
      (≅-trans (Extensional.wire-resp (port-tensor (port-id A) (port-id B)) (port-id (A ⊗₀ B))
        (λ { (inj₁ _) → refl ; (inj₂ _) → refl })) (wire-id (A ⊗₀ B))))

private
  variable
    A B C D E F : Interface

  opaque
    tensor-composition : {f : Network A B} {g : Network C D} {h : Network B E} {i : Network D F} →
      ((h ∘ f) ⊗₁ (i ∘ g)) ≅ ((h ⊗₁ i) ∘ (f ⊗₁ g))
    tensor-composition {f = f} {g} {h} {i} = ≅-sym (Exchange.plugging-tensor-interchange f g h i)

    tensor-congruence : {f f′ : Network A B} {g g′ : Network C D} →
      f ≅ f′ → g ≅ g′ → (f ⊗₁ g) ≅ (f′ ⊗₁ g′)
    tensor-congruence = TensorIso.tensor-congruence

tensor-bifunctor : Bifunctor OpenCSP OpenCSP OpenCSP
tensor-bifunctor = record
  { F₀ = uncurry _⊗₀_ ; F₁ = uncurry _⊗₁_
  ; identity = identity-tensor
  ; homomorphism = tensor-composition
  ; F-resp-≈ = uncurry tensor-congruence }
