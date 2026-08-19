{-# OPTIONS --safe --without-K #-}

-- SPIKE: Mealy machines over an arbitrary symmetric monoidal category.
--
-- `CategoricalCrypto.SFunM` is this construction at `𝒱 = Kleisli 𝒫` written
-- elementwise; the point of the spike is to find out which structure the layer
-- actually uses.  The answer here: a symmetric monoidal `𝒱` for the state
-- pairing, plus a point and a discard on each state object.  No monad appears —
-- the monad's strength and commutativity are exactly what make a Kleisli
-- category symmetric monoidal (`Categories.Category.Monoidal.Construction.Kleisli`).

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Data.Nat.Base using (ℕ; zero; suc)
open import Level using (_⊔_)
open import Relation.Binary using (IsEquivalence)

module CategoricalCrypto.SFunM.Spike.Mealy {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided using (σ⇒)
open MonoidalUtilities.Shorthands monoidal
open Equiv

private variable A B C D P Q R X Y Z : Obj

------------------------------------------------------------------------
-- The two structural shuffles the construction needs

-- Swaps the second and third factor; its own inverse.
swp : (P ⊗₀ Q) ⊗₀ R ⇒ (P ⊗₀ R) ⊗₀ Q
swp = α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒

-- Moves the second interface factor into the state's slot.
tuck : P ⊗₀ (Q ⊗₀ R) ⇒ (P ⊗₀ R) ⊗₀ Q
tuck = α⇐ ∘ id ⊗₁ σ⇒

untuck : (P ⊗₀ R) ⊗₀ Q ⇒ P ⊗₀ (Q ⊗₀ R)
untuck = id ⊗₁ σ⇒ ∘ α⇒

-- The middle-four interchange, built from `swp` on the state pair.  Also its own
-- inverse, and equal to `Categories.Category.Monoidal.Interchange.Braided`'s
-- `swapInner`, which routes the braiding through the interface pair instead
-- (`Ω≈Ω′` in `Spike.Interchange`).
Ω : (P ⊗₀ Q) ⊗₀ (X ⊗₀ Y) ⇒ (P ⊗₀ X) ⊗₀ (Q ⊗₀ Y)
Ω = α⇒ ∘ swp ⊗₁ id ∘ α⇐

------------------------------------------------------------------------
-- Machines

-- A state object comes with a point (the initial state) and a discard (what
-- `eval` does with the final state).  Both are real data at the instances that
-- matter: in a Kleisli category `unit` is neither initial nor terminal, so
-- `point` is a possibly-effectful initial state where `SFunᵉ` has a pure `init`,
-- and a degenerate `discard` annihilates every trace.  Imposing affineness on
-- `𝒱` (a copy-discard structure) is what would make `discard` canonical and let
-- this field go.
record State : Set (o ⊔ ℓ) where
  field
    obj     : Obj
    point   : unit ⇒ obj
    discard : obj ⇒ unit

open State

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

open Machine

------------------------------------------------------------------------
-- The four ways a step can act on a paired state or a paired interface

-- The left factor of a paired state acts on the whole interface.
onL : (P ⊗₀ X ⇒ P ⊗₀ Y) → (P ⊗₀ Q) ⊗₀ X ⇒ (P ⊗₀ Q) ⊗₀ Y
onL k = swp ∘ k ⊗₁ id ∘ swp

-- The right factor of a paired state acts on the whole interface.
onR : (Q ⊗₀ X ⇒ Q ⊗₀ Y) → (P ⊗₀ Q) ⊗₀ X ⇒ (P ⊗₀ Q) ⊗₀ Y
onR k = α⇐ ∘ id ⊗₁ k ∘ α⇒

-- The whole state acts on the first interface factor.
slot₁ : (P ⊗₀ X ⇒ P ⊗₀ Y) → P ⊗₀ (X ⊗₀ Z) ⇒ P ⊗₀ (Y ⊗₀ Z)
slot₁ k = α⇒ ∘ k ⊗₁ id ∘ α⇐

-- The whole state acts on the second interface factor.
slot₂ : (P ⊗₀ X ⇒ P ⊗₀ Y) → P ⊗₀ (Z ⊗₀ X) ⇒ P ⊗₀ (Z ⊗₀ Y)
slot₂ k = untuck ∘ k ⊗₁ id ∘ tuck

------------------------------------------------------------------------
-- Composition

idᴹ : Machine A A
idᴹ = record { state = Iˢ ; step = id }

infixr 9 _∘ᴹ_

_∘ᴹ_ : Machine B C → Machine A B → Machine A C
g ∘ᴹ f = record { state = state g ⊛ state f ; step = onL (step g) ∘ onR (step f) }

------------------------------------------------------------------------
-- Finite unrollings

-- The tensor power of the interface: `pow n A` is the `n`-fold `⊗`.  It plays
-- the role of `List A` in the elementwise layer, which is why the elementwise
-- `trace` needs no structure beyond the monad while this one needs `𝒱`.
pow : ℕ → Obj → Obj
pow zero    A = unit
pow (suc n) A = A ⊗₀ pow n A

run : (f : Machine A B) (n : ℕ) → St f ⊗₀ pow n A ⇒ St f ⊗₀ pow n B
run f zero    = id
run f (suc n) = slot₂ (run f n) ∘ slot₁ (step f)

eval : (f : Machine A B) (n : ℕ) → pow n A ⇒ pow n B
eval f n = λ⇒ ∘ discard (state f) ⊗₁ id ∘ run f n ∘ point (state f) ⊗₁ id ∘ λ⇐

infix 4 _≈ᵉ_

_≈ᵉ_ : Machine A B → Machine A B → Set e
f ≈ᵉ g = ∀ n → eval f n ≈ eval g n

≈ᵉ-isEquivalence : IsEquivalence (_≈ᵉ_ {A} {B})
≈ᵉ-isEquivalence = record
  { refl  = λ _ → refl
  ; sym   = λ f≈g n → sym (f≈g n)
  ; trans = λ f≈g g≈h n → trans (f≈g n) (g≈h n)
  }
