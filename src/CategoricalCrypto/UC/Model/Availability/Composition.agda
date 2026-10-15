{-# OPTIONS --safe --without-K --guardedness #-}

-- The direct PM testing presheaf supplies the quantitative instance; the
-- middle-four interchange and unit laws use only the sealed symmetric tensor.

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Reasoning
import Categories.Morphism.Reasoning

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.UC.Model.Quantitative
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Symmetric

import CategoricalCrypto.UC.Quantitative.Availability.Composition as Composition
import CategoricalCrypto.UC.Quantitative.Availability.Standard as Standard
module CategoricalCrypto.UC.Model.Availability.Composition where

module QCompositionᵒ = Composition.Serial ℚ-ordered QSetupᵒ
open QCompositionᵒ using (T₀; sub)

private
  module G = MonoidalCategory 𝔾ᵒ

open G
open Categories.Category.Monoidal.Reasoning monoidal
open Categories.Morphism.Reasoning U

module Structuralᵒ = Standard.Structural ℚ-ordered 𝔾ᵒ symmetricᵒ
module Standardᵒ = Standard.Standard ℚ-ordered 𝔾ᵒ symmetricᵒ Qᵒ

pairingᵒ : Composition.Parallel.Pairing ℚ-ordered QSetupᵒ monoidal
pairingᵒ = Standardᵒ.pairing

module QParallelᵒ = Composition.Parallel.Laws ℚ-ordered QSetupᵒ monoidal pairingᵒ

private variable
  A B C D X P : Obj

close-unit-compose : (f : A ⇒ T₀ unit B) (u : B ⇒ T₀ unit C)
                   → (unitorˡ.from ∘ (sub unitorˡ.from ∘ (u QCompositionᵒ.∙ f)))
                     ≈ (unitorˡ.from ∘ u) ∘ (unitorˡ.from ∘ f)
close-unit-compose = Structuralᵒ.unit-close-compose

no-adversary-compose : (a : X ⇒ unit) (c : P ⇒ unit)
                       (f : A ⇒ T₀ X B) (u : B ⇒ T₀ P C)
                     → unitorˡ.from ∘ QCompositionᵒ.close (QCompositionᵒ.cap-compose a c) (u QCompositionᵒ.∙ f)
                       ≈ (unitorˡ.from ∘ QCompositionᵒ.close c u) ∘ (unitorˡ.from ∘ QCompositionᵒ.close a f)
no-adversary-compose a c f u =
  ∘-resp-≈ʳ (QCompositionᵒ.close-compose a c f u)
  ○ close-unit-compose (QCompositionᵒ.close a f) (QCompositionᵒ.close c u)

no-adversary-parallel : (a : X ⇒ unit) (c : P ⇒ unit)
                        (f : A ⇒ T₀ X B) (u : C ⇒ T₀ P D)
  → unitorˡ.from ∘ QCompositionᵒ.close (QCompositionᵒ.cap-compose a c) (QParallelᵒ.pair f u)
    ≈ (unitorˡ.from ∘ QCompositionᵒ.close a f) ⊗₁ (unitorˡ.from ∘ QCompositionᵒ.close c u)
no-adversary-parallel a c f u = begin
  unitorˡ.from ∘ QCompositionᵒ.close (QCompositionᵒ.cap-compose a c) (QParallelᵒ.pair f u)
    ≈⟨ refl⟩∘⟨ QParallelᵒ.close-parallel a c f u ⟩
  unitorˡ.from ∘ ((unitorˡ.from ⊗₁ id) ∘ (Structuralᵒ.middle4 ∘
    (QCompositionᵒ.close a f ⊗₁ QCompositionᵒ.close c u)))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  unitorˡ.from ∘ (((unitorˡ.from ⊗₁ id) ∘ Structuralᵒ.middle4) ∘
    (QCompositionᵒ.close a f ⊗₁ QCompositionᵒ.close c u))
    ≈⟨ sym-assoc ⟩
  (unitorˡ.from ∘ ((unitorˡ.from ⊗₁ id) ∘ Structuralᵒ.middle4)) ∘
    (QCompositionᵒ.close a f ⊗₁ QCompositionᵒ.close c u)
    ≈⟨ Structuralᵒ.unit-middle4 ⟩∘⟨refl ⟩
  (unitorˡ.from ⊗₁ unitorˡ.from) ∘ (QCompositionᵒ.close a f ⊗₁ QCompositionᵒ.close c u)
    ≈˘⟨ ⊗.homomorphism ⟩
  (unitorˡ.from ∘ QCompositionᵒ.close a f) ⊗₁ (unitorˡ.from ∘ QCompositionᵒ.close c u) ∎
