{-# OPTIONS --safe --without-K #-}

-- Mealy machines over a symmetric monoidal category, with *simulation* as the
-- hom equality.
--
-- The base structure used is exactly: a symmetric monoidal `𝒱` for pairing
-- states, plus a point and a discard on each state object.  No monad appears —
-- a monad's strength and commutativity are what make its Kleisli category
-- symmetric monoidal, and that is all the construction consumes.
--
-- The hom equality lives in `CategoricalCrypto.Machines.Sim`, which needs a
-- class of state maps this module does not.

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Level

module CategoricalCrypto.Machines.Core {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided
open MonoidalUtilities.Shorthands monoidal

private variable A B P Q R X Y : Obj

-- Swaps the second and third state factor; its own inverse.
swp : (P ⊗₀ Q) ⊗₀ R ⇒ (P ⊗₀ R) ⊗₀ Q
swp = α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒

------------------------------------------------------------------------
-- Machines

-- A state object comes with a point (the initial state) and a discard.  Both
-- are real data at the instances that matter: in a Kleisli category `unit` is
-- neither initial nor terminal, so `point` is a possibly-effectful initial
-- state, and a degenerate `discard` annihilates every trace.  Imposing
-- affineness on `𝒱` is what would make `discard` canonical.
record State : Set (o ⊔ ℓ) where
  field
    obj     : Obj
    point   : unit ⇒ obj
    discard : obj ⇒ unit

open State public

Iˢ : State
Iˢ = record { obj = unit ; point = id ; discard = id }

infixr 9 _⊛_

_⊛_ : State → State → State
S ⊛ T = record
  { obj     = obj S ⊗₀ obj T
  ; point   = point S ⊗₁ point T ∘ λ⇐
  ; discard = λ⇒ ∘ discard S ⊗₁ discard T
  }

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

-- The left factor of a paired state acts on the whole interface.
onL : (P ⊗₀ X ⇒ P ⊗₀ Y) → (P ⊗₀ Q) ⊗₀ X ⇒ (P ⊗₀ Q) ⊗₀ Y
onL k = swp ∘ k ⊗₁ id ∘ swp

-- The right factor of a paired state acts on the whole interface.
onR : (Q ⊗₀ X ⇒ Q ⊗₀ Y) → (P ⊗₀ Q) ⊗₀ X ⇒ (P ⊗₀ Q) ⊗₀ Y
onR k = α⇐ ∘ id ⊗₁ k ∘ α⇒

-- `onR` with the codomain state freed, hence definitionally `onR` wherever
-- both apply; the general form accepts a state braiding.
onRᵍ : (Q ⊗₀ X ⇒ R ⊗₀ Y) → (P ⊗₀ Q) ⊗₀ X ⇒ (P ⊗₀ R) ⊗₀ Y
onRᵍ k = α⇐ ∘ id ⊗₁ k ∘ α⇒

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
