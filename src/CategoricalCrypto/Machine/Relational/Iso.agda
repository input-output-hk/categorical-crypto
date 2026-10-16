{-# OPTIONS --safe #-}

module CategoricalCrypto.Machine.Relational.Iso where

open import Categories.Category.Monoidal.Construction.Reverse
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Category as Old
import CategoricalCrypto.Machine.Core as M
import CategoricalCrypto.Machine.Iso as Iso
import CategoricalCrypto.Machine.MonoidalCategory as OldM
import CategoricalCrypto.Machine.UC as OldUC
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Category
open import CategoricalCrypto.Machine.Relational.Isomorphism
open import CategoricalCrypto.Machine.Relational.Model
import CategoricalCrypto.Machine.Relational.Wiring as W

private variable A B C D : Channel

all-states-compose : (g : M.Machine B C) (f : M.Machine A B)
  → all-states (g M.∘ f) ≈ᴿ (all-states g W.∘ all-states f)
all-states-compose g f = lift-iso Iso.≅ᴹ-refl (λ _ → tt , tt) (λ _ → tt)

all-states-tensor : (f : M.Machine A B) (g : M.Machine C D)
  → all-states (f M.⊗₁ g) ≈ᴿ (all-states f W.⊗₁ all-states g)
all-states-tensor f g = lift-iso Iso.≅ᴹ-refl (λ _ → tt , tt) (λ _ → tt)

-- Feedback is preserved separately; no traced-category bundle is asserted.
all-states-trace : (f : M.Machine (A ⊗₀ C) (B ⊗₀ C))
  → all-states (M.tr f) ≈ᴿ W.trace (all-states f)
all-states-trace f = ≈ᴿ-refl

all-states-functor : Functor Old.MachineCategory 𝔾ᴿ
all-states-functor = record
  { F₀ = λ A → A ; F₁ = all-states
  ; identity = lift-iso Iso.≅ᴹ-refl (λ _ → refl) (λ _ → tt)
  ; homomorphism = λ { {f = f} {g} → all-states-compose g f }
  ; F-resp-≈ = all-states-cong
  }

private
  module Plain = IsStrongMonoidalFunctor (idF-IsStrongMonoidal OldM.machine-monoidal-category)
  module Reverse = IsStrongMonoidalFunctor
    (idF-IsStrongMonoidal (Reverse-MonoidalCategory OldM.machine-monoidal-category))

Iso→native : StrongMonoidalFunctor OldM.machine-monoidal-category 𝔾ᴿᵐ
Iso→native = record
  { F = all-states-functor
  ; isStrongMonoidal = record
    { ε = record { from = W.id ; to = W.id
                 ; iso = record { isoˡ = identityˡ ; isoʳ = identityˡ } }
    ; ⊗-homo = niHelper record
      { η = λ _ → W.id ; η⁻¹ = λ _ → W.id
      ; commute = λ f → total-iso (Plain.⊗-homo.⇒.commute f)
          (λ _ → (tt , tt) , refl) (λ _ → refl , tt)
      ; iso = λ _ → record { isoˡ = identityˡ ; isoʳ = identityˡ } }
    ; associativity = total-iso Plain.associativity
        (λ _ → ((refl , refl) , refl) , tt) (λ _ → (tt , (refl , refl)) , refl)
    ; unitaryˡ = total-iso Plain.unitaryˡ (λ _ → ((refl , refl) , refl) , tt) (λ _ → tt)
    ; unitaryʳ = total-iso Plain.unitaryʳ (λ _ → ((refl , refl) , refl) , tt) (λ _ → tt)
    }
  }

-- This source is exactly Machine.UC.machines, whose tensor is reversed.
-- It is a categorical connection, not a morphism of the different UC test spaces.
IsoUC→native-reverse : StrongMonoidalFunctor OldUC.machines 𝔾ᴿʳ
IsoUC→native-reverse = record
  { F = all-states-functor
  ; isStrongMonoidal = record
    { ε = record { from = W.id ; to = W.id
                 ; iso = record { isoˡ = identityˡ ; isoʳ = identityˡ } }
    ; ⊗-homo = niHelper record
      { η = λ _ → W.id ; η⁻¹ = λ _ → W.id
      ; commute = λ f → total-iso (Reverse.⊗-homo.⇒.commute f)
          (λ _ → (tt , tt) , refl) (λ _ → refl , tt)
      ; iso = λ _ → record { isoˡ = identityˡ ; isoʳ = identityˡ } }
    ; associativity = total-iso Reverse.associativity
        (λ _ → ((refl , refl) , refl) , tt) (λ _ → (tt , (refl , refl)) , refl)
    ; unitaryˡ = total-iso Reverse.unitaryˡ (λ _ → ((refl , refl) , refl) , tt) (λ _ → tt)
    ; unitaryʳ = total-iso Reverse.unitaryʳ (λ _ → ((refl , refl) , refl) , tt) (λ _ → tt)
    }
  }
