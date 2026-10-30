{-# OPTIONS --safe --without-K #-}

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U

module Categories.Category.Monoidal.Traced.Ext
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (T : Traced M) where

open Category C
open Traced T
open U.Shorthands M
open BProps.Shorthands braided

open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric
open import Categories.Morphism.Reasoning C

private variable A B X Y : Obj

fuse : {f : (A ⊗₀ X) ⊗₀ Y ⇒ (B ⊗₀ X) ⊗₀ Y} → trace (trace f) ≈ trace (α⇒ ∘ f ∘ α⇐)
fuse = trace-resp-≈ (trace-resp-≈
         (⟺ ((refl⟩∘⟨ assoc) ○ cancelˡ associator.isoˡ ○ cancelʳ associator.isoˡ)))
     ○ vanishing₂

trace-comm : {f : (A ⊗₀ X) ⊗₀ Y ⇒ (B ⊗₀ X) ⊗₀ Y} → trace (trace f) ≈ trace (trace (β ∘ f ∘ β))
trace-comm {f = f} =
  fuse ○ trace-resp-≈ (insertʳ (⊗-cancel identity² commutative)) ○ slide ○ trace-resp-≈ (⟺ swap) ○ ⟺ fuse
  where
  swap : α⇒ ∘ (β ∘ f ∘ β) ∘ α⇐ ≈ id ⊗₁ σ⇒ ∘ (α⇒ ∘ f ∘ α⇐) ∘ id ⊗₁ σ⇒
  swap = begin
    α⇒ ∘ (β ∘ f ∘ β) ∘ α⇐
      ≈⟨ refl⟩∘⟨ assoc ○ pullˡ α⇒-β ○ assoc ⟩
    id ⊗₁ σ⇒ ∘ α⇒ ∘ (f ∘ β) ∘ α⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (assoc ○ refl⟩∘⟨ β-α⇐) ⟩
    id ⊗₁ σ⇒ ∘ α⇒ ∘ f ∘ α⇐ ∘ id ⊗₁ σ⇒
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ sym-assoc ○ sym-assoc) ⟩
    id ⊗₁ σ⇒ ∘ (α⇒ ∘ f ∘ α⇐) ∘ id ⊗₁ σ⇒ ∎
