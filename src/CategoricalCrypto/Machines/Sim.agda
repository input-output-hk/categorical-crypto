{-# OPTIONS --safe --without-K #-}

-- Simulation relation between machines

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Subcategory
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Level
import Relation.Binary.Construct.Closure.Equivalence as EqC

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame

module CategoricalCrypto.Machines.Sim
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) (𝒫 : WideSymmetricMonoidalSubcategory 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open Equiv
open Frame 𝒱
open MonoidalUtilities.Shorthands monoidal
open WideSymmetricMonoidalSubcategory 𝒫

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B : Obj
                 f g h : Machine A B
                 S : State

record _≲_ (f g : Machine A B) : Set (ℓ ⊔ e) where
  constructor sim
  field θ       : St f ⇒ St g
        θ-selected : Selected θ
        θ-point : θ ∘ point (state f) ≈ point (state g)
        θ-step  : θ ⊗₁ id ∘ step f ≈ step g ∘ θ ⊗₁ id

open _≲_ public

infix 4 _≲_ _≈ᴹ_

_≈ᴹ_ : Machine A B → Machine A B → Set (o ⊔ ℓ ⊔ e)
_≈ᴹ_ = EqC.EqClosure _≲_

mk-cong : {k k′ : obj S ⊗₀ A ⇒ obj S ⊗₀ B} → k ≈ k′ → mk S k ≲ mk S k′
mk-cong eq = sim id selected-id identityˡ (elimˡ ⊗.identity ○ eq ○ ⟺ (elimʳ ⊗.identity))

≲-refl : f ≲ f
≲-refl = mk-cong refl

≲-trans : f ≲ g → g ≲ h → f ≲ h
≲-trans s t = record
  { θ       = θ t ∘ θ s
  ; θ-selected = selected-∘ (θ-selected t) (θ-selected s)
  ; θ-point = pullʳ (θ-point s) ○ θ-point t
  ; θ-step  = (split₁ˡ ⟩∘⟨refl) ○ glue (θ-step t) (θ-step s) ○ (refl⟩∘⟨ ⟺ split₁ˡ)
  }

≲⇒≈ᴹ : f ≲ g → f ≈ᴹ g
≲⇒≈ᴹ = EqC.return

≲⇒≈ᴹ˘ : f ≲ g → g ≈ᴹ f
≲⇒≈ᴹ˘ s = EqC.symmetric _≲_ (EqC.return s)

infixr 9 _○ᴹ_

reflᴹ : f ≈ᴹ f
reflᴹ = EqC.reflexive _≲_

⟺ᴹ : f ≈ᴹ g → g ≈ᴹ f
⟺ᴹ = EqC.symmetric _≲_

_○ᴹ_ : f ≈ᴹ g → g ≈ᴹ h → f ≈ᴹ h
_○ᴹ_ = EqC.transitive _≲_

collapseˡ : {k : (unit ⊗₀ obj S) ⊗₀ A ⇒ (unit ⊗₀ obj S) ⊗₀ B} {k′ : obj S ⊗₀ A ⇒ obj S ⊗₀ B}
          → λ⇒ ⊗₁ id ∘ k ≈ k′ ∘ λ⇒ ⊗₁ id → mk (Iˢ ⊛ S) k ≲ mk S k′
collapseˡ {S = S} = sim λ⇒ selected-λ⇒ (λ-point S)

collapseʳ : {k : (obj S ⊗₀ unit) ⊗₀ A ⇒ (obj S ⊗₀ unit) ⊗₀ B} {k′ : obj S ⊗₀ A ⇒ obj S ⊗₀ B}
          → ρ⇒ ⊗₁ id ∘ k ≈ k′ ∘ ρ⇒ ⊗₁ id → mk (S ⊛ Iˢ) k ≲ mk S k′
collapseʳ {S = S} = sim ρ⇒ selected-ρ⇒ (ρ-point S)
