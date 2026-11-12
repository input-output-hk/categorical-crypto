{-# OPTIONS --safe --without-K #-}

module Categories.Coherence.Symmetric.Test.Tactic where

open import Data.Product
open import Level
open import Function using (case_of_)

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U
open import Categories.Coherence.Symmetric.Tactic
open import Categories.Functor using (Functor)
import Categories.Morphism as Morphism

module _ {o} {ℓ} {e} (Cˢ : SymmetricMonoidalCategory o ℓ e) where
  open SymmetricMonoidalCategory Cˢ
  open BProps.Shorthands braided
  open U.Shorthands monoidal
  open Morphism U using (_≅_)

  module _ (A B D E : Obj) (f : A ⇒ B) (g : D ⇒ E) where
    natural : σ⇒ ∘ (f ⊗₁ g) ≈ (g ⊗₁ f) ∘ σ⇒
    natural = solve-smc Cˢ

    conjugate : σ⇒ ∘ (g ⊗₁ f) ∘ σ⇒ ≈ f ⊗₁ g
    conjugate = solve-smc Cˢ

    explicit-component : braiding.⇒.η (B , E) ∘ (f ⊗₁ g) ≈ (g ⊗₁ f) ∘ braiding.⇒.η (A , D)
    explicit-component = solve-smc Cˢ

    iso-projection : _≅_.from (braiding.FX≅GX {B , E}) ∘ (f ⊗₁ g) ≈ (g ⊗₁ f) ∘ σ⇒
    iso-projection = solve-smc Cˢ

    derived-tensor : Functor.F₁ (-⊗ D) f ≈ f ⊗₁ id
    derived-tensor = solve-smc Cˢ

    derived-tensor-shorthand : Functor.₁ (D ⊗-) f ≈ id ⊗₁ f
    derived-tensor-shorthand = solve-smc Cˢ

    derived-naturality : σ⇒ ∘ Functor.₁ (-⊗ D) f ≈ Functor.F₁ (D ⊗-) f ∘ σ⇒
    derived-naturality = solve-smc Cˢ

  module _ (A B : Obj) (f g : A ⇒ A) (μ : A ⊗₀ B ⇒ A)
           (η : unit ⇒ A ⊗₀ B) (ε : A ⊗₀ B ⇒ unit) where
    involution : σ⇒ {B} {A} ∘ σ⇒ {A} {B} ≈ id
    involution = solve-smc Cˢ

    symmetric-iso : braided-iso.to {A} {B} ≈ σ⇒ {B} {A}
    symmetric-iso = solve-smc Cˢ

    pi-prefix : ∀ {D E} (h : D ⇒ E) → σ⇒ ∘ (f ⊗₁ h) ≈ (h ⊗₁ f) ∘ σ⇒
    pi-prefix = solve-smc Cˢ

    repeated-distinct : σ⇒ ∘ ((f ∘ g ∘ f) ⊗₁ g) ∘ σ⇒ ≈ (g ⊗₁ (f ∘ g ∘ f))
    repeated-distinct = solve-smc Cˢ

    composite-arity : σ⇒ ∘ (μ ⊗₁ η) ≈ (η ⊗₁ μ) ∘ σ⇒
    composite-arity = solve-smc Cˢ

    empty-output : σ⇒ ∘ (ε ⊗₁ f) ≈ (f ⊗₁ ε) ∘ σ⇒
    empty-output = solve-smc Cˢ

    scalar : (s : unit ⇒ unit) → λ⇒ ∘ (s ⊗₁ f) ≈ ρ⇒ ∘ (f ⊗₁ s) ∘ σ⇒
    scalar s = solve-smc Cˢ

    unitors : λ⇒ {A} ∘ λ⇐ ≈ ρ⇒ ∘ ρ⇐
    unitors = solve-smc Cˢ

    test-triangle : (id ⊗₁ λ⇒) ∘ α⇒ {A} {unit} {B} ≈ ρ⇒ ⊗₁ id
    test-triangle = solve-smc Cˢ

    inverse-associator : α⇐ {A} {B} {A} ∘ α⇒ ≈ id
    inverse-associator = solve-smc Cˢ

    hexagon : (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ {A} {B} ⊗₁ id {A}) ≈ α⇒ ∘ σ⇒ ∘ α⇒
    hexagon = solve-smc Cˢ

    inverse-opaque : id ∘ σ⇐ {A} {B} ≈ σ⇐
    inverse-opaque = solve-smc Cˢ

    inverse-projection : id ∘ _≅_.to (braiding.FX≅GX {A , B}) ≈
      _≅_.to (braiding.FX≅GX {A , B})
    inverse-projection = solve-smc Cˢ

    opaque
      box₁ box₂ : A ⇒ A
      box₁ = f ∘ f
      box₂ = f ∘ f

    opaque-repetitions : σ⇒ ∘ ((box₁ ∘ box₂ ∘ box₁) ⊗₁ box₂) ≈
      (box₂ ⊗₁ (box₁ ∘ box₂ ∘ box₁)) ∘ σ⇒
    opaque-repetitions = solve-smc Cˢ
