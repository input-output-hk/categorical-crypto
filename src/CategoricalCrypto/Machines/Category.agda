{-# OPTIONS --safe --without-K #-}

-- The category of Mealy machines, with the simulation zig-zag as its equality.
--
-- Each law is one simulation: the unit laws collapse a trivial state factor
-- (`λ⇒`/`ρ⇒`), associativity re-brackets the state tree (`α⇒`), and the
-- congruence pairs the two given state maps.  Nothing here unrolls a machine,
-- because a simulation is a statement about one step.

open import Categories.Category.Core
open import Categories.Category.EquivClosureHelper
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
open import Categories.Coherence.Monoidal
open import Categories.Coherence.Monoidal.Tactic
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Data.Fin
open import Data.Product
open import Data.Vec using (_∷_; [])
open import Level

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Machines.Category
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) (𝒫 : PureSub 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open Frame 𝒱
open BraidedProps.Shorthands braided
open MonoidalUtilities.Shorthands monoidal
open PureSub 𝒫
open Sim 𝒱 𝒫

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric
open import Categories.Morphism.Reasoning U

private variable A B C D P Q R X Y : Obj

-- Associativity's step obligations are three squares, one per leaf of
-- `(P ⊗₀ Q) ⊗₀ R`: re-bracketing the state tree leaves each leaf's action where
-- it was.  `onR-α` and `onLR-α` are decided by the monoidal solver: every
-- crossing occurs at the same arity on both sides, hence as an opaque box.
onR-α : (k : R ⊗₀ X ⇒ R ⊗₀ Y) → α⇒ {P} {Q} ⊗₁ id ∘ onR k ≈ onR (onR k) ∘ α⇒ ⊗₁ id
onR-α k = solve-mor 𝕄

onLR-α : (g : Q ⊗₀ X ⇒ Q ⊗₀ Y)
       → α⇒ ⊗₁ id ∘ onL (onR g)
       ≈ onR {P = P} (onL {Q = R} g) ∘ α⇒ ⊗₁ id
onLR-α g = solve-mor 𝕄

-- Not decided by the solver: `onL {Q = Q ⊗₀ R}` crosses the block
-- `σ⇒ {Q ⊗₀ R} {X}` where the nested `onL (onL …)` crosses `σ⇒ {Q} {X}` and
-- `σ⇒ {R} {X}` separately, and the normalizer never splits or merges a crossing
-- block.  So the two blocks are split by hand and the residue goes to
-- `solveMor!` with the four atomic crossings named as generators, the object
-- parser being unable to recover them itself; the objects are bound on the
-- left because the solver's atom vector needs them.
onL-α : (h : P ⊗₀ X ⇒ P ⊗₀ Y)
      → α⇒ {P} {Q} ⊗₁ id ∘ onL (onL h)
      ≈ onL {Q = Q ⊗₀ R} h ∘ α⇒ ⊗₁ id
onL-α {P = P} {X = X} {Y = Y} {Q = Q} {R = R} h = solved ○ ⟺ (((refl⟩∘⟨ refl⟩⊗⟨ σ-splitˡ ⟩∘⟨refl) ⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ refl⟩⊗⟨ σ-splitʳ ⟩∘⟨refl)) ⟩∘⟨refl)
  where
    solved : α⇒ {P} {Q} ⊗₁ id ∘ onL {Q = R} (onL h)
           ≈ ((α⇐ ∘ id ⊗₁ ((α⇐ ∘ (id ⊗₁ σ⇒ ∘ (α⇒ ∘ σ⇒ ⊗₁ id))) ∘ α⇐) ∘ α⇒)
              ∘ (h ⊗₁ id
              ∘ (α⇐ ∘ id ⊗₁ (α⇒ ∘ (((σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ σ⇒) ∘ α⇒)) ∘ α⇒)))
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
          swpQᵢ = S.α⇐ S.∘ S.id S.⊗₁ σqx S.∘ S.α⇒
          swpQₒ = S.α⇐ S.∘ S.id S.⊗₁ σyq S.∘ S.α⇒
          swpRᵢ = S.α⇐ S.∘ S.id S.⊗₁ σrx S.∘ S.α⇒
          swpRₒ = S.α⇐ S.∘ S.id S.⊗₁ σyr S.∘ S.α⇒
          splitˡ = (S.α⇐ S.∘ (S.id S.⊗₁ σyr S.∘ (S.α⇒ S.∘ σyq S.⊗₁ S.id))) S.∘ S.α⇐
          splitʳ = S.α⇒ S.∘ (((σqx S.⊗₁ S.id S.∘ S.α⇐) S.∘ S.id S.⊗₁ σrx) S.∘ S.α⇒)
          onLᵗ = swpQₒ S.∘ hᵗ S.⊗₁ S.id S.∘ swpQᵢ
      in solveMor! (S.α⇒ S.⊗₁ S.id S.∘ swpRₒ S.∘ onLᵗ S.⊗₁ S.id S.∘ swpRᵢ)
                   (((S.α⇐ S.∘ S.id S.⊗₁ splitˡ S.∘ S.α⇒)
                     S.∘ (hᵗ S.⊗₁ S.id
                     S.∘ (S.α⇐ S.∘ S.id S.⊗₁ splitʳ S.∘ S.α⇒)))
                    S.∘ S.α⇒ S.⊗₁ S.id)

opaque
  unfolding _∘ᴹ_

  assoc-∘ᴹ : {f : Machine A B} {g : Machine B C} {h : Machine C D}
           → ((h ∘ᴹ g) ∘ᴹ f) ≲ (h ∘ᴹ (g ∘ᴹ f))
  assoc-∘ᴹ {f = f} {g} {h} = sim α⇒ pure-α⇒
    (⊛-assoc-point (state h) (state g) (state f))
    ( (refl⟩∘⟨ (onL-∘ ⟩∘⟨refl))
    ○ (refl⟩∘⟨ assoc)
    ○ pullˡ (onL-α (step h))
    ○ assoc
    ○ (refl⟩∘⟨ pullˡ (onLR-α (step g)))
    ○ (refl⟩∘⟨ assoc)
    ○ (refl⟩∘⟨ (refl⟩∘⟨ onR-α (step f)))
    ○ (refl⟩∘⟨ sym-assoc)
    ○ (refl⟩∘⟨ ((⟺ onR-∘) ⟩∘⟨refl))
    ○ sym-assoc )

  identityˡ-∘ᴹ : {f : Machine A B} → (idᴹ ∘ᴹ f) ≲ f
  identityˡ-∘ᴹ = collapseˡ ((refl⟩∘⟨ ((onL-id ⟩∘⟨refl) ○ identityˡ)) ○ onR-collapseˡ)

  identityʳ-∘ᴹ : {f : Machine A B} → (f ∘ᴹ idᴹ) ≲ f
  identityʳ-∘ᴹ = collapseʳ ((refl⟩∘⟨ ((refl⟩∘⟨ onR-id) ○ identityʳ)) ○ onL-collapseʳ)

  ∘ᴹ-resp-≲ : {f h : Machine B C} {g i : Machine A B} → f ≲ h → g ≲ i → (f ∘ᴹ g) ≲ (h ∘ᴹ i)
  ∘ᴹ-resp-≲ {f = f} {h} {g} {i} u v = record
    { θ       = θ u ⊗₁ θ v
    ; θ-pure  = pure-⊗₁ (θ-pure u) (θ-pure v)
    ; θ-point = ⊛-point₂ (state f) (state h) (state g) (state i) (θ-point u) (θ-point v)
    ; θ-step  = pullˡ (onL-sim (θ-step u)) ○ assoc
              ○ (refl⟩∘⟨ onR-sim (θ-step v)) ○ sym-assoc
    }

Mealy-Category : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
Mealy-Category = categoryHelperᵉ record
  { Obj       = Obj
  ; _⇒_       = Machine
  ; _≈_       = _≲_
  ; id        = idᴹ
  ; _∘_       = _∘ᴹ_
  ; assoc     = assoc-∘ᴹ
  ; identityˡ = identityˡ-∘ᴹ
  ; identityʳ = identityʳ-∘ᴹ
  ; ∘-resp-≈  = ∘ᴹ-resp-≲
  }

∘ᴹ-resp-≈ᴹ : {f h : Machine B C} {g i : Machine A B} → f ≈ᴹ h → g ≈ᴹ i → (f ∘ᴹ g) ≈ᴹ (h ∘ᴹ i)
∘ᴹ-resp-≈ᴹ = Category.∘-resp-≈ Mealy-Category
