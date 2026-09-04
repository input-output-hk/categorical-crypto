{-# OPTIONS --safe --without-K #-}

-- Re-bracketing a Mealy composite's state tree leaves each leaf's action where
-- it was; these three squares are the step obligations of `_∘ᴹ_`'s
-- associativity, one per leaf of `(P ⊗₀ Q) ⊗₀ R`.
--
-- `onR-α` and `onLR-α` are decided by the monoidal solver: every crossing
-- occurs at the same arity on both sides, hence as an opaque box.  `onL-α` is
-- not — `onL {Q = Q ⊗₀ R}` crosses the block `σ⇒ {Q ⊗₀ R} {X}` where the
-- nested `onL (onL …)` crosses `σ⇒ {Q} {X}` and `σ⇒ {R} {X}` separately, and
-- the normalizer never splits or merges a crossing block (`lim-hexagon` in
-- `Categories.Coherence.Monoidal.Test.Limitations`).  So the two blocks are
-- split by hand and the residue goes to `solveMor!` with the four atomic
-- crossings named as generators, the object parser being unable to recover
-- them itself.

open import Categories.Category.Monoidal.Bundle
open import Categories.Coherence.Monoidal
open import Categories.Coherence.Monoidal.Tactic
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Data.Fin
open import Data.Product
open import Data.Vec using (_∷_; [])

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame

module CategoricalCrypto.Machines.Reassoc {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided
open MonoidalUtilities.Shorthands monoidal
open Core 𝒱
open Frame 𝒱

open import Categories.Category.Monoidal.Reasoning monoidal

private variable P Q R X Y : Obj

onR-α : (k : R ⊗₀ X ⇒ R ⊗₀ Y)
      → α⇒ {P} {Q} {R} ⊗₁ id ∘ onR {P = P ⊗₀ Q} k
      ≈ onR {P = P} (onR {P = Q} k) ∘ α⇒ ⊗₁ id
onR-α k = solve-mor 𝕄

onLR-α : (g : Q ⊗₀ X ⇒ Q ⊗₀ Y)
       → α⇒ {P} {Q} {R} ⊗₁ id ∘ onL {Q = R} (onR {P = P} g)
       ≈ onR {P = P} (onL {Q = R} g) ∘ α⇒ ⊗₁ id
onLR-α g = solve-mor 𝕄

-- The objects are bound on the left because the solver's atom vector needs them.
onL-α : (h : P ⊗₀ X ⇒ P ⊗₀ Y)
      → α⇒ {P} {Q} {R} ⊗₁ id ∘ onL {Q = R} (onL {Q = Q} h)
      ≈ onL {Q = Q ⊗₀ R} h ∘ α⇒ ⊗₁ id
onL-α {P = P} {X = X} {Y = Y} {Q = Q} {R = R} h = solved ○ ⟺ (split ⟩∘⟨refl)
  where
    split : onL {Q = Q ⊗₀ R} h
          ≈ (α⇐ ∘ id {P} ⊗₁ ((α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id))) ∘ α⇐) ∘ α⇒)
            ∘ (h ⊗₁ id
            ∘ (α⇐ ∘ id {P} ⊗₁ (α⇒ ∘ (((σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘ α⇒)) ∘ α⇒))
    split = (refl⟩∘⟨ refl⟩⊗⟨ σ-splitˡ ⟩∘⟨refl)
              ⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ refl⟩⊗⟨ σ-splitʳ ⟩∘⟨refl)

    solved : α⇒ {P} {Q} {R} ⊗₁ id ∘ onL {Q = R} (onL {Q = Q} h)
           ≈ ((α⇐ ∘ id {P} ⊗₁ ((α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id))) ∘ α⇐) ∘ α⇒)
              ∘ (h ⊗₁ id
              ∘ (α⇐ ∘ id {P} ⊗₁ (α⇒ ∘ (((σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘ α⇒)) ∘ α⇒)))
             ∘ α⇒ ⊗₁ id
    solved =
      let vs = P ∷ Q ∷ R ∷ X ∷ Y ∷ []
          open MorAtoms 𝕄 vs
          open MorSolve 𝕄 vs
               ( ((V (# 0) ⊗ᵒ V (# 3) , V (# 0) ⊗ᵒ V (# 4)) , h)
               ∷ ((V (# 1) ⊗ᵒ V (# 3) , V (# 3) ⊗ᵒ V (# 1)) , σ⇒)
               ∷ ((V (# 2) ⊗ᵒ V (# 3) , V (# 3) ⊗ᵒ V (# 2)) , σ⇒)
               ∷ ((V (# 4) ⊗ᵒ V (# 1) , V (# 1) ⊗ᵒ V (# 4)) , σ⇒)
               ∷ ((V (# 4) ⊗ᵒ V (# 2) , V (# 2) ⊗ᵒ V (# 4)) , σ⇒) ∷ [] )
          p = V (# 0); q = V (# 1); r = V (# 2); x = V (# 3); y = V (# 4)
          hᵗ = gen (# 0); σqx = gen (# 1); σrx = gen (# 2)
          σyq = gen (# 3); σyr = gen (# 4)
          swpQᵢ = S.α⇐ S.∘ S.id {p} S.⊗₁ σqx S.∘ S.α⇒
          swpQₒ = S.α⇐ S.∘ S.id {p} S.⊗₁ σyq S.∘ S.α⇒
          swpRᵢ = S.α⇐ S.∘ S.id {p ⊗ᵒ q} S.⊗₁ σrx S.∘ S.α⇒
          swpRₒ = S.α⇐ S.∘ S.id {p ⊗ᵒ q} S.⊗₁ σyr S.∘ S.α⇒
          splitˡ = (S.α⇐ S.∘ (S.id {q} S.⊗₁ σyr S.∘ (S.α⇒ S.∘ σyq S.⊗₁ S.id {r})))
                     S.∘ S.α⇐
          splitʳ = S.α⇒ S.∘ (((σqx S.⊗₁ S.id {r} S.∘ S.α⇐) S.∘ S.id {q} S.⊗₁ σrx)
                     S.∘ S.α⇒)
          onLᵗ = swpQₒ S.∘ hᵗ S.⊗₁ S.id {q} S.∘ swpQᵢ
      in solveMor! (S.α⇒ S.⊗₁ S.id {y} S.∘ swpRₒ S.∘ onLᵗ S.⊗₁ S.id {r} S.∘ swpRᵢ)
                   (((S.α⇐ S.∘ S.id {p} S.⊗₁ splitˡ S.∘ S.α⇒)
                     S.∘ (hᵗ S.⊗₁ S.id {q ⊗ᵒ r}
                     S.∘ (S.α⇐ S.∘ S.id {p} S.⊗₁ splitʳ S.∘ S.α⇒)))
                    S.∘ S.α⇒ S.⊗₁ S.id {x})
