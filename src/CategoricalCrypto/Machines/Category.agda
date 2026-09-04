{-# OPTIONS --safe --without-K #-}

-- The category of Mealy machines, with the simulation zig-zag as its equality.
--
-- Each law is one simulation: the unit laws collapse a trivial state factor
-- (`λ⇒`/`ρ⇒`), associativity re-brackets the state tree (`α⇒`), and the
-- congruence pairs the two given state maps.  Nothing here unrolls a machine,
-- because a simulation is a statement about one step.

open import Categories.Category.Core using (Category)
open import Categories.Category.EquivClosureHelper using (categoryHelperᵉ)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Pure using (PureSub)
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Level using (_⊔_)

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Reassoc as Reassoc
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Machines.Category
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) (𝒫 : PureSub 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open Equiv
open Frame 𝒱
open MonoidalUtilities.Shorthands monoidal
open PureSub 𝒫
open Reassoc 𝒱
open Sim 𝒱 𝒫

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B C D : Obj

assoc-∘ᴹ : {f : Machine A B} {g : Machine B C} {h : Machine C D}
         → ((h ∘ᴹ g) ∘ᴹ f) ≲ (h ∘ᴹ (g ∘ᴹ f))
assoc-∘ᴹ {f = f} {g} {h} = sim α⇒ pure-α⇒
  (⊛-assoc-discard (state h) (state g) (state f))
  (⊛-assoc-point (state h) (state g) (state f))
  ( (refl⟩∘⟨ (onL-∘ ⟩∘⟨refl))
  ○ (refl⟩∘⟨ assoc)
  ○ pullˡ (onL-α (step h))
  ○ assoc
  ○ (refl⟩∘⟨ pullˡ (onLR-α (step g)))
  ○ (refl⟩∘⟨ assoc)
  ○ (refl⟩∘⟨ (refl⟩∘⟨ onR-α (step f)))
  ○ (refl⟩∘⟨ sym-assoc)
  ○ (refl⟩∘⟨ ((⟺ onRᵍ-∘) ⟩∘⟨refl))
  ○ sym-assoc )

identityˡ-∘ᴹ : {f : Machine A B} → (idᴹ ∘ᴹ f) ≲ f
identityˡ-∘ᴹ = collapseˡ ((refl⟩∘⟨ ((onL-id ⟩∘⟨refl) ○ identityˡ)) ○ onR-collapseˡ)

identityʳ-∘ᴹ : {f : Machine A B} → (f ∘ᴹ idᴹ) ≲ f
identityʳ-∘ᴹ = collapseʳ ((refl⟩∘⟨ ((refl⟩∘⟨ onR-id) ○ identityʳ)) ○ onL-collapseʳ)

∘ᴹ-resp-≲ : {f h : Machine B C} {g i : Machine A B}
          → f ≲ h → g ≲ i → (f ∘ᴹ g) ≲ (h ∘ᴹ i)
∘ᴹ-resp-≲ {f = f} {h} {g} {i} u v = record
  { θ         = θ u ⊗₁ θ v
  ; θ-pure    = pure-⊗₁ (θ-pure u) (θ-pure v)
  ; θ-discard = ⊛-discard₂ (state f) (state h) (state g) (state i)
                           (θ-discard u) (θ-discard v)
  ; θ-point   = ⊛-point₂ (state f) (state h) (state g) (state i)
                         (θ-point u) (θ-point v)
  ; θ-step    = pullˡ (onL-sim (θ-step u)) ○ assoc
              ○ (refl⟩∘⟨ onR-sim (θ-step v)) ○ sym-assoc
  }

Mealy-Category : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
Mealy-Category = categoryHelperᵉ record
  { Obj       = Obj
  ; _⇒_       = Machine
  ; _≈_       = _≲_
  ; id        = idᴹ
  ; _∘_       = _∘ᴹ_
  ; assoc     = assoc-∘ᴹ
  ; identityˡ = identityˡ-∘ᴹ
  ; identityʳ = identityʳ-∘ᴹ
  ; ∘-resp-≈  = ∘ᴹ-resp-≲
  }

∘ᴹ-resp-≈ᴹ : {f h : Machine B C} {g i : Machine A B}
           → f ≈ᴹ h → g ≈ᴹ i → (f ∘ᴹ g) ≈ᴹ (h ∘ᴹ i)
∘ᴹ-resp-≈ᴹ = Category.∘-resp-≈ Mealy-Category
