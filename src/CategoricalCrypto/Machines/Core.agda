{-# OPTIONS --safe --without-K #-}

-- Mealy machines over a symmetric monoidal category.

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Level

module CategoricalCrypto.Machines.Core {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open MonoidalUtilities.Shorthands monoidal

open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric

private variable A B P Q R X Y : Obj

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

record Machine (A B : Obj) : Set (o ⊔ ℓ) where
  constructor mk
  field state : State

  St : Obj
  St = obj state

  field step : St ⊗₀ A ⇒ St ⊗₀ B

open Machine public

------------------------------------------------------------------------
-- The ways a step can act on a paired state

onL : (P ⊗₀ X ⇒ P ⊗₀ Y) → (P ⊗₀ Q) ⊗₀ X ⇒ (P ⊗₀ Q) ⊗₀ Y
onL k = β ∘ k ⊗₁ id ∘ β

onR : (Q ⊗₀ X ⇒ R ⊗₀ Y) → (P ⊗₀ Q) ⊗₀ X ⇒ (P ⊗₀ R) ⊗₀ Y
onR k = α⇐ ∘ id ⊗₁ k ∘ α⇒

------------------------------------------------------------------------
-- Composition

idᴹ : Machine A A
idᴹ = mk Iˢ id

infixr 9 _∘ᴹ_

opaque
  _∘ᴹ_ : Machine B P → Machine A B → Machine A P
  g ∘ᴹ f = mk (state g ⊛ state f) (onL (step g) ∘ onR (step f))
