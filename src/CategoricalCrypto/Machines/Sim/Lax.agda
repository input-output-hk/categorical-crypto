{-# OPTIONS --safe --without-K #-}

-- Simulation up to an initialization prefix.
--
-- `Machines.Sim`'s generator equates the two points on the nose, which is too
-- strict for a machine that carries a dead-weight component: a scalar
-- `σ : unit ⇒ unit` buried in a composite contributes its own initialization to
-- the run and nothing else, and no state map makes that disappear.  `_≲ˡ[_]_`
-- records exactly that gap — step and state map as strict as `_≲_`, the point
-- only up to a scalar prefix; its run-level reading is `Machines.Run.Lax`.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure

open import Level

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Machines.Sim.Lax
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) (𝒫 : PureSub 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open PureSub 𝒫

infix 4 _≲ˡ[_]_

record _≲ˡ[_]_ {A B : Obj} (f : Machine A B) (σ : unit ⇒ unit) (g : Machine A B)
       : Set (ℓ ⊔ e) where
  field
    θˡ       : St f ⇒ St g
    θˡ-pure  : Pure θˡ
    θˡ-point : θˡ ∘ point (state f) ≈ point (state g) ∘ σ
    θˡ-step  : θˡ ⊗₁ id ∘ step f ≈ step g ∘ θˡ ⊗₁ id

open _≲ˡ[_]_ public
