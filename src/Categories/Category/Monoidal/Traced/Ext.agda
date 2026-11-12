{-# OPTIONS --safe --without-K #-}

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U
open import Categories.Coherence.Symmetric.Tactic

module Categories.Category.Monoidal.Traced.Ext
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (T : Traced M) where

open Category C
open Traced T
open U.Shorthands M
open BProps.Shorthands braided

open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric
open import Categories.Morphism.Reasoning C

private
  variable A B D E X Y Z : Obj

  Cˢ : SymmetricMonoidalCategory o ℓ e
  Cˢ = record { U = C ; monoidal = M ; symmetric = symmetric }

trace-β : trace (β {A} {X} {X}) ≈ id
trace-β = superposing ○ (refl⟩⊗⟨ yanking) ○ ⊗.identity

trace-β′ : {g : A ⊗₀ X ⇒ B} → trace (g ⊗₁ id ∘ β) ≈ g
trace-β′ = tightenₗ ○ elimʳ trace-β

fuse : {f : (A ⊗₀ X) ⊗₀ Y ⇒ (B ⊗₀ X) ⊗₀ Y} → trace (trace f) ≈ trace (α⇒ ∘ f ∘ α⇐)
fuse = trace-resp-≈ (trace-resp-≈
         (⟺ ((refl⟩∘⟨ assoc) ○ cancelˡ associator.isoˡ ○ cancelʳ associator.isoˡ)))
     ○ vanishing₂

trace-comm : {f : (A ⊗₀ X) ⊗₀ Y ⇒ (B ⊗₀ X) ⊗₀ Y} → trace (trace f) ≈ trace (trace (β ∘ f ∘ β))
trace-comm {f = f} =
  fuse ○ trace-resp-≈ (insertʳ (⊗-cancel identity² commutative)) ○ slide ○ trace-resp-≈ (⟺ swap) ○ ⟺ fuse
  where
  swap : α⇒ ∘ (β ∘ f ∘ β) ∘ α⇐ ≈ id ⊗₁ σ⇒ ∘ (α⇒ ∘ f ∘ α⇐) ∘ id ⊗₁ σ⇒
  swap = solve-smc Cˢ

threading : (A ⊗₀ Y ⇒ B ⊗₀ X) → (A ⊗₀ Z) ⊗₀ Y ⇒ (B ⊗₀ Z) ⊗₀ X
threading f = β ∘ f ⊗₁ id ∘ β

-- composing f & g along X/Y and taking the trace doesn't depend on the order of composition
abstract
  feedback-interchange : {f : A ⊗₀ Y ⇒ B ⊗₀ X} {g : E ⊗₀ X ⇒ D ⊗₀ Y} →
    trace ((α⇐ ∘ id ⊗₁ g ∘ α⇒) ∘ threading f) ≈ trace (threading f ∘ α⇐ ∘ id ⊗₁ g ∘ α⇒)
  feedback-interchange {A = A} {Y = Y} {B = B} {X = X} {E = E} {D = D} {f} {g} =
    ⟺ (trace-resp-≈ (tightenᵣ ○ trace-β′ ⟩∘⟨refl))
    ○ trace-comm {f = split}
    ○ trace-resp-≈ (trace-resp-≈ exchange ○ tightenᵣ ○ trace-β′ ⟩∘⟨refl)
    where
      split : ((A ⊗₀ E) ⊗₀ Y) ⊗₀ X ⇒ ((B ⊗₀ D) ⊗₀ Y) ⊗₀ X
      split = ((α⇐ ∘ id ⊗₁ g ∘ α⇒) ⊗₁ id ∘ β) ∘ threading f ⊗₁ id

      exchange : β ∘ split ∘ β ≈ (threading f ⊗₁ id ∘ β) ∘ (α⇐ ∘ id ⊗₁ g ∘ α⇒) ⊗₁ id
      exchange = solve-smc Cˢ
