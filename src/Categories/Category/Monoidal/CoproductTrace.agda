{-# OPTIONS --safe --without-K #-}

open import Categories.Category.Cocartesian.Monoidal
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Subcategory
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Distributive as MD
open import Level

module Categories.Category.Monoidal.CoproductTrace {o ℓ e}
  (𝒱 : SymmetricMonoidalCategory o ℓ e) (dist : MD.MonoidalDistributive 𝒱)
  (𝒫 : WideSymmetricMonoidalSubcategory 𝒱) where

open SymmetricMonoidalCategory 𝒱
open MD.MonoidalDistributive dist
open WideSymmetricMonoidalSubcategory 𝒫

private variable A B X Y P : Obj

record CoproductTrace : Set (levelOfTerm 𝒱) where
  field coproduct-traced : Traced (CocartesianMonoidal.+-monoidal cocartesian)

  open Traced coproduct-traced using (trace)

  field
    trace-uniform : (κ : X ⇒ Y) → Selected κ
                  → {f : A + X ⇒ B + X} {g : A + Y ⇒ B + Y}
                  → g ∘ (id +₁ κ) ≈ (id +₁ κ) ∘ f → trace g ≈ trace f
    tensor-strength : (f : A + X ⇒ B + X)
                    → trace (δ⇐ ∘ id {P} ⊗₁ f ∘ distributeˡ) ≈ id ⊗₁ trace f
