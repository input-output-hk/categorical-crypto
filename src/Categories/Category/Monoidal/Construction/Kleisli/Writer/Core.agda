{-# OPTIONS --safe --without-K #-}

open import Categories.Category
open import Categories.Category.Construction.Kleisli
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Braided.Properties as BProps
open import Categories.Category.Monoidal.Symmetric
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Traced.Ext as TracedExt
import Categories.Category.Monoidal.Utilities as U
open import Categories.Coherence.Symmetric.Tactic
open import Categories.Monad using (Monad)
open import Categories.Monad.Construction.Action
open import Categories.Monad.Construction.Action.Commutative
import Categories.Monad.Strong.Properties as SP
open import Categories.Object.CommutativeMonoid
open import Categories.Object.Monoid

module Categories.Category.Monoidal.Construction.Kleisli.Writer.Core
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} where

open Category C
open U.Shorthands M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Morphism.Reasoning C

private variable A B D X Y : Obj

module Normalization (S : Symmetric M) (W : Monoid M) where
  open Symmetric S
  open BProps.Shorthands braided
  open Monoid W using () renaming (Carrier to E)

  private
    module Action = Monad (ActionM M W)
    module K = Category (Kleisli (ActionM M W))
    module Strength = SP.Left.Shorthands (actionStrength S W)

    Cˢ : SymmetricMonoidalCategory o ℓ e
    Cˢ = record { U = C ; monoidal = M ; symmetric = S }

  opaque
    normalize-tightenₗ : (f : B ⇒ E ⊗₀ D) (g : A ⊗₀ X ⇒ E ⊗₀ (B ⊗₀ X)) →
      α⇐ ∘ ((α⇒ ∘ f ⊗₁ id) K.∘ g) ≈ (Action.μ.η _ ∘ id ⊗₁ f) ⊗₁ id ∘ (α⇐ ∘ g)
    normalize-tightenₗ f g = solve-smc Cˢ

    normalize-tightenᵣ : (f : B ⊗₀ X ⇒ E ⊗₀ (D ⊗₀ X)) (g : A ⇒ E ⊗₀ B) →
      α⇐ ∘ (f K.∘ (α⇒ ∘ g ⊗₁ id)) ≈
      Action.μ.η _ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ (α⇐ ∘ f) ∘ α⇒) ∘ g ⊗₁ id
    normalize-tightenᵣ f g = solve-smc Cˢ

    normalize-vanishing₂ : (f : A ⊗₀ (X ⊗₀ Y) ⇒ E ⊗₀ (B ⊗₀ (X ⊗₀ Y))) →
      α⇐ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ α⇐ ∘ f ∘ α⇒) ≈ α⇐ ∘ (α⇐ ∘ f) ∘ α⇒
    normalize-vanishing₂ f = solve-smc Cˢ

    normalize-superposing : (f : A ⊗₀ X ⇒ E ⊗₀ (B ⊗₀ X)) (Y : Obj) →
      α⇐ ∘ id ⊗₁ α⇐ ∘ (Strength.σ ∘ id {Y} ⊗₁ f) ∘ α⇒ ≈
      Strength.σ ⊗₁ id ∘ (α⇐ ∘ id {Y} ⊗₁ (α⇐ ∘ f) ∘ α⇒)
    normalize-superposing f Y = solve-smc Cˢ

    normalize-yanking : (X : Obj) → α⇐ ∘ K.id ∘ σ⇒ {X} {X} ≈ K.id ⊗₁ id ∘ σ⇒
    normalize-yanking X = normalize
      where
        normalize : α⇐ ∘ Action.η.η (X ⊗₀ X) ∘ σ⇒ ≈ Action.η.η X ⊗₁ id ∘ σ⇒
        normalize = solve-smc Cˢ

module Trace (T : Traced M) (W : Monoid M) where
  open Traced T
  open BProps.Shorthands braided
  open Monoid W using () renaming (Carrier to E)
  open Normalization symmetric W

  private
    module K = Category (Kleisli (ActionM M W))
    module Strength = SP.Left.Shorthands (actionStrength symmetric W)

  traceW : A ⊗₀ X ⇒ E ⊗₀ (B ⊗₀ X) → A ⇒ E ⊗₀ B
  traceW f = trace (α⇐ ∘ f)

  traceW-resp-≈ : {f g : A ⊗₀ X ⇒ E ⊗₀ (B ⊗₀ X)} → f ≈ g → traceW f ≈ traceW g
  traceW-resp-≈ eq = trace-resp-≈ (refl⟩∘⟨ eq)

  vanishing₁W : {f : A ⇒ E ⊗₀ B} → traceW {X = unit} (α⇒ ∘ f ⊗₁ id) ≈ f
  vanishing₁W = trace-resp-≈ (cancelˡ associator.isoˡ) ○ vanishing₁

  tightenₗW : {f : B ⇒ E ⊗₀ D} {g : A ⊗₀ X ⇒ E ⊗₀ (B ⊗₀ X)} →
    traceW ((α⇒ ∘ f ⊗₁ id) K.∘ g) ≈ f K.∘ traceW g
  tightenₗW {f = f} {g} = trace-resp-≈ (normalize-tightenₗ f g) ○ tightenₗ

  tightenᵣW : {f : B ⊗₀ X ⇒ E ⊗₀ (D ⊗₀ X)} {g : A ⇒ E ⊗₀ B} →
    traceW (f K.∘ α⇒ ∘ g ⊗₁ id) ≈ traceW f K.∘ g
  tightenᵣW {f = f} {g} =
    trace-resp-≈ (normalize-tightenᵣ f g)
    ○ tightenₗ ○ refl⟩∘⟨ (tightenᵣ ○ superposing ⟩∘⟨refl) ○ sym-assoc

  vanishing₂W : {f : A ⊗₀ (X ⊗₀ Y) ⇒ E ⊗₀ (B ⊗₀ (X ⊗₀ Y))} →
    traceW (traceW (id ⊗₁ α⇐ ∘ f ∘ α⇒)) ≈ traceW f
  vanishing₂W {f = f} =
    trace-resp-≈ (⟺ tightenₗ ○ trace-resp-≈ (normalize-vanishing₂ f)) ○ vanishing₂

  superposingW : {f : A ⊗₀ X ⇒ E ⊗₀ (B ⊗₀ X)} →
    traceW (id ⊗₁ α⇐ ∘ (Strength.σ ∘ id {Y} ⊗₁ f) ∘ α⇒) ≈ Strength.σ ∘ id {Y} ⊗₁ traceW f
  superposingW {Y = Y} {f} =
    trace-resp-≈ (normalize-superposing f Y) ○ tightenₗ ○ refl⟩∘⟨ superposing

  yankingW : traceW (K.id ∘ σ⇒ {X} {X}) ≈ K.id
  yankingW {X} = trace-resp-≈ (normalize-yanking X) ○ tightenₗ ○ elimʳ yanking

module Sliding (T : Traced M) (W : CommutativeMonoid (Traced.braided T)) where
  open Traced T
  open BProps.Shorthands braided
  open CommutativeMonoid W using (monoid) renaming (Carrier to E; μ to m; commutative to μ-comm)
  open Trace T monoid
  open TracedExt T

  private
    module Action = Monad (ActionM M monoid)
    module K = Category (Kleisli (ActionM M monoid))
    module Strength = SP.Left.Shorthands (actionStrength symmetric monoid)

    Cˢ : SymmetricMonoidalCategory o ℓ e
    Cˢ = record { U = C ; monoidal = M ; symmetric = symmetric }

  collect : (E ⊗₀ B) ⊗₀ E ⇒ E ⊗₀ B
  collect = Action.μ.η _ ∘ id ⊗₁ σ⇒ ∘ α⇒

  opaque
    collect-comm : Action.μ.η _ ∘ σ⇒ ≈ collect {B}
    collect-comm {B} = collect-swap ○ μ-comm ⟩⊗⟨refl ⟩∘⟨refl ○ sym-assoc
      where
        collect-swap : (m ⊗₁ id ∘ α⇐) ∘ σ⇒ ≈ (m ∘ σ⇒) ⊗₁ id {B} ∘ α⇐ ∘ id ⊗₁ σ⇒ ∘ α⇒
        collect-swap = solve-smc Cˢ

    normalize-slideˡ : (f : A ⊗₀ Y ⇒ E ⊗₀ B ⊗₀ X) (g : X ⇒ E ⊗₀ Y) →
      α⇐ ∘ f K.∘ Strength.σ ∘ id ⊗₁ g ≈
      (Action.μ.η _ ∘ σ⇒) ⊗₁ id ∘
      (threading (α⇐ ∘ f) ∘ α⇐ ∘ id ⊗₁ (g ∘ λ⇒) ∘ α⇒) ∘ ρ⇐ ⊗₁ id
    normalize-slideˡ f g = solve-smc Cˢ

    normalize-slideʳ : (f : A ⊗₀ Y ⇒ E ⊗₀ (B ⊗₀ X)) (g : X ⇒ E ⊗₀ Y) →
      α⇐ ∘ ((Strength.σ ∘ id ⊗₁ g) K.∘ f) ≈
      collect ⊗₁ id ∘ ((α⇐ ∘ id ⊗₁ (g ∘ λ⇒) ∘ α⇒) ∘ threading (α⇐ ∘ f)) ∘ ρ⇐ ⊗₁ id
    normalize-slideʳ f g = solve-smc Cˢ

  slideW : (f : A ⊗₀ Y ⇒ E ⊗₀ (B ⊗₀ X)) (g : X ⇒ E ⊗₀ Y) →
    traceW (f K.∘ (Strength.σ ∘ id ⊗₁ g)) ≈ traceW ((Strength.σ ∘ id ⊗₁ g) K.∘ f)
  slideW f g =
    trace-resp-≈ (normalize-slideˡ f g) ○ tightenₗ
    ○ refl⟩∘⟨ (tightenᵣ ○ (⟺ feedback-interchange ⟩∘⟨refl))
    ○ collect-comm ⟩∘⟨refl ○ refl⟩∘⟨ ⟺ tightenᵣ
    ○ ⟺ tightenₗ ○ trace-resp-≈ (⟺ (normalize-slideʳ f g))
