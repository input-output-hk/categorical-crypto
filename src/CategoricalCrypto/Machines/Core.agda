{-# OPTIONS --safe --without-K #-}

-- Mealy machines over a symmetric monoidal category.

open import Level

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
open import Categories.Coherence.Symmetric.Tactic

module CategoricalCrypto.Machines.Core {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided
open MonoidalUtilities.Shorthands monoidal

open import Categories.Category.Monoidal.Properties monoidal
open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric

private variable A B P : Obj

-- `point` is the initial state; over a Kleisli base it may be effectful (a
-- distribution over states).
record State : Set (o ⊔ ℓ) where
  field
    obj   : Obj
    point : unit ⇒ obj

open State public

Iˢ : State
Iˢ = record { obj = unit ; point = id }

infixr 9 _⊛_

_⊛_ : State → State → State
S ⊛ T = record { obj = obj S ⊗₀ obj T ; point = point S ⊗₁ point T ∘ λ⇐ }

⊛-∘-point : {S T S′ T′ : State} {u : obj S ⇒ obj T} {v : obj S′ ⇒ obj T′}
          → u ∘ point S ≈ point T → v ∘ point S′ ≈ point T′
          → u ⊗₁ v ∘ point (S ⊛ S′) ≈ point (T ⊛ T′)
⊛-∘-point e₁ e₂ = pullˡ (⟺ ⊗.homomorphism ○ e₁ ⟩⊗⟨ e₂)

λ-point : (S : State) → λ⇒ ∘ point (Iˢ ⊛ S) ≈ point S
λ-point S = pullˡ unitorˡ-commute-from ○ cancelʳ unitorˡ.isoʳ

ρ-point : (S : State) → ρ⇒ ∘ point (S ⊛ Iˢ) ≈ point S
ρ-point S = pullˡ unitorʳ-commute-from ○ cancelʳ (⟺ coherence₃ ⟩∘⟨refl ○ unitorˡ.isoʳ)

⊛-swap-point : (S T : State) → σ⇒ ∘ point (S ⊛ T) ≈ point (T ⊛ S)
⊛-swap-point S T = solve-smc 𝒱

⊛-assoc-point : (S T R : State) → α⇒ ∘ point ((S ⊛ T) ⊛ R) ≈ point (S ⊛ (T ⊛ R))
⊛-assoc-point S T R = solve-smc 𝒱

record Machine (A B : Obj) : Set (o ⊔ ℓ) where
  constructor mk
  field state : State

  St : Obj
  St = obj state

  field step : St ⊗₀ A ⇒ St ⊗₀ B

open Machine public

------------------------------------------------------------------------
-- Composition

idᴹ : Machine A A
idᴹ = mk Iˢ id

infixr 9 _∘ᴹ_

opaque
  _∘ᴹ_ : Machine B P → Machine A B → Machine A P
  g ∘ᴹ f = mk (state g ⊛ state f) (onL (step g) ∘ onR (step f))
