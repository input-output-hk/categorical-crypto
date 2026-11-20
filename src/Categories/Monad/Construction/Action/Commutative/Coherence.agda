{-# OPTIONS --safe --without-K #-}

module Categories.Monad.Construction.Action.Commutative.Coherence where

open import Categories.Category.Core
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Core
open import Categories.Category.Monoidal.Symmetric
import Categories.Category.Monoidal.Braided.Properties as BP
import Categories.Category.Monoidal.Utilities as MU
open import Categories.Coherence.Symmetric.Tactic
open import Categories.Monad using (Monad)
open import Categories.Monad.Construction.Action
open import Categories.Object.Monoid

module Wiring {o ℓ e} {C : Category o ℓ e} {M : Monoidal C}
  (S : Symmetric M) (E : Category.Obj C) where
  open Category C
  open Monoidal M
  open BP.Shorthands (Symmetric.braided S)
  open MU.Shorthands M

  private variable A B : Obj

  strength-map : A ⊗₀ E ⊗₀ B ⇒ E ⊗₀ A ⊗₀ B
  strength-map = α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐

  effect-permute : (E ⊗₀ A) ⊗₀ (E ⊗₀ B) ⇒ (E ⊗₀ E) ⊗₀ (A ⊗₀ B)
  effect-permute = α⇐ ∘ id ⊗₁ strength-map ∘ α⇒

module Laws {o ℓ e} {C : Category o ℓ e} {M : Monoidal C}
  (S : Symmetric M) (W : Monoid M) where
  open Category C
  open Monoidal M
  open BP.Shorthands (Symmetric.braided S)
  open MU.Shorthands M
  open Monoid W using (Carrier)
  open Wiring S Carrier

  private
    module Action = Monad (ActionM M W)
    variable A A′ B B′ : Obj

    SC : SymmetricMonoidalCategory o ℓ e
    SC = record { U = C; monoidal = M; symmetric = S }

  opaque
    natural : (f : A ⇒ A′) (g : B ⇒ B′) →
      strength-map ∘ f ⊗₁ id ⊗₁ g ≈ id ⊗₁ f ⊗₁ g ∘ strength-map
    natural f g = solve-smc SC

    strength-unit : (A : Obj) → (id ⊗₁ λ⇒) ∘ strength-map {unit} {A} ≈ λ⇒
    strength-unit A = solve-smc SC

    strength-η : (A B : Obj) →
      strength-map {A} {B} ∘ id ⊗₁ Action.η.η B ≈ Action.η.η (A ⊗₀ B)
    strength-η A B = solve-smc SC

    strength-μ : (A B : Obj) →
      Action.μ.η (A ⊗₀ B) ∘ id ⊗₁ strength-map {A} {B} ∘ strength-map
      ≈ strength-map ∘ id ⊗₁ Action.μ.η B
    strength-μ A B = solve-smc SC

    left-normal : (A B : Obj) →
      (Action.μ.η (A ⊗₀ B) ∘ (id ⊗₁ α⇒)) ∘ strength-map {Carrier ⊗₀ A} {B}
      ≈ ((Monoid.μ W ∘ σ⇒) ⊗₁ id) ∘ effect-permute
    left-normal A B = solve-smc SC

    right-normal : (A B : Obj) →
      (Action.μ.η (A ⊗₀ B) ∘ id ⊗₁ strength-map {A} {B}) ∘ α⇒
      ≈ Monoid.μ W ⊗₁ id ∘ effect-permute
    right-normal A B = solve-smc SC

    strength-assoc : (A B D : Obj) →
      id ⊗₁ α⇒ ∘ strength-map {A ⊗₀ B} {D} ≈ strength-map ∘ id ⊗₁ strength-map ∘ α⇒
    strength-assoc A B D = solve-smc SC

    right-strength : (A B : Obj) → id ⊗₁ σ⇒ ∘ strength-map {B} {A} ∘ σ⇒ ≈ α⇒
    right-strength A B = solve-smc SC
