{-# OPTIONS --safe --without-K #-}

-- Mealy machines over a symmetric monoidal category; the hom equality is
-- simulation (`Machines.Sim`).  No monad appears: a monad's strength and
-- commutativity are what make its Kleisli category symmetric monoidal, and that
-- is all the construction consumes.

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Level

module CategoricalCrypto.Machines.Core {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open MonoidalUtilities.Shorthands monoidal

open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric

private variable A B P Q R X Y : Obj

------------------------------------------------------------------------
-- Machines

-- `point` is the initial state, possibly effectful: in a Kleisli category
-- `unit` is not initial.
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
  field
    state : State

  St : Obj
  St = obj state

  field
    step : St ⊗₀ A ⇒ St ⊗₀ B

open Machine public

mk : (S : State) → obj S ⊗₀ A ⇒ obj S ⊗₀ B → Machine A B
mk S k = record { state = S ; step = k }

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

-- Keep composite endpoints nominal during conversion.  The few laws that read
-- the paired state or step opt in with `unfolding _∘ᴹ_`.
opaque
  _∘ᴹ_ : Machine B P → Machine A B → Machine A P
  g ∘ᴹ f = mk (state g ⊛ state f) (onL (step g) ∘ onR (step f))
