{-# OPTIONS --safe --without-K #-}

-- Coh(ℐ): the monoidal category of coherence isomorphisms of a monoidal
-- category ℐ. It is the free monoidal category over `Ob ℐ` with NO morphism
-- generators, so every hom is a structural coherence iso.
--
-- The interpretation functor ⟦-⟧ : Coh(ℐ) → ℐ is faithful.

module Categories.CoherenceIsos where

open import Level
open import Data.Empty

open import Categories.Category
open import Categories.Category.Groupoid
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Reasoning as MonR
open import Categories.Coherence.Monoidal.MacLane
open import Categories.FreeMonoidal
open import Categories.Functor hiding (id)
open import Categories.Functor.Monoidal
open import Categories.Functor.Properties
import Categories.Morphism.Reasoning as MR

open import Class.DecEq

module Coherence {o ℓ e : Level} (ℐ : MonoidalCategory o ℓ e) where
  private module ℐ = MonoidalCategory ℐ

  cohData : FreeMonoidalData
  cohData = record { v = Mon ; X = ℐ.Obj ; mor = λ _ _ → ⊥ }

  ffd : FreeFunctorData cohData
  ffd = record { ⟦v⟧ = fromMC ℐ noSymmetric ; ⟦_⟧ᵖ₀ = λ x → x ; ⟦_⟧ᵖ₁ = λ () }

  open FreeFunctorData ffd public using (⟦_⟧₀)
  open FreeFunctor ffd public
    using (⟦_⟧₁; ⟦⟧-resp-≈; freeFunctor; isMonoidal-freeFunctor; FreeMonoidalM)

  Coh : MonoidalCategory o o o
  Coh = FreeMonoidalM

  ⟦-⟧ : Functor (MonoidalCategory.U Coh) ℐ.U
  ⟦-⟧ = freeFunctor

  -- ⟦-⟧ as a (strict) monoidal functor: structure maps ε, ⊗-homo are ℐ.id.
  ⟦-⟧-monoidal : MonoidalFunctor Coh ℐ
  ⟦-⟧-monoidal = record { F = freeFunctor ; isMonoidal = isMonoidal-freeFunctor }

  -- Coh(ℐ) is a groupoid
  private module FM = FreeMonoidal cohData
  open FM
  open FM public using (Var)

  inv : ∀ {A B} → HomTerm A B → HomTerm B A
  inv (var ())
  inv id       = id
  inv (g ∘ f)  = inv f ∘ inv g
  inv (f ⊗₁ g) = inv f ⊗₁ inv g
  inv λ⇒       = λ⇐
  inv λ⇐       = λ⇒
  inv ρ⇒       = ρ⇐
  inv ρ⇐       = ρ⇒
  inv α⇒       = α⇐
  inv α⇐       = α⇒

  open MonR (MonoidalCategory.monoidal Coh)
  open MR FreeMonoidal

  inv-isoˡ : ∀ {A B} (f : HomTerm A B) → FreeMonoidal [ inv f ∘ f ≈ id ]
  inv-isoˡ (var ())
  inv-isoˡ id       = idˡ
  inv-isoˡ (g ∘ f)  = cancelInner (inv-isoˡ g) ○ inv-isoˡ f
  inv-isoˡ (f ⊗₁ g) = ⟺ ⊗-∘-dist ○ (inv-isoˡ f ⟩⊗⟨ inv-isoˡ g) ○ id⊗id≈id
  inv-isoˡ λ⇒       = λ⇐∘λ⇒≈id
  inv-isoˡ λ⇐       = λ⇒∘λ⇐≈id
  inv-isoˡ ρ⇒       = ρ⇐∘ρ⇒≈id
  inv-isoˡ ρ⇐       = ρ⇒∘ρ⇐≈id
  inv-isoˡ α⇒       = α⇐∘α⇒≈id
  inv-isoˡ α⇐       = α⇒∘α⇐≈id

  inv-isoʳ : ∀ {A B} (f : HomTerm A B) → FreeMonoidal [ f ∘ inv f ≈ id ]
  inv-isoʳ (var ())
  inv-isoʳ id       = idˡ
  inv-isoʳ (g ∘ f)  = cancelInner (inv-isoʳ f) ○ inv-isoʳ g
  inv-isoʳ (f ⊗₁ g) = ⟺ ⊗-∘-dist ○ (inv-isoʳ f ⟩⊗⟨ inv-isoʳ g) ○ id⊗id≈id
  inv-isoʳ λ⇒       = λ⇒∘λ⇐≈id
  inv-isoʳ λ⇐       = λ⇐∘λ⇒≈id
  inv-isoʳ ρ⇒       = ρ⇒∘ρ⇐≈id
  inv-isoʳ ρ⇐       = ρ⇐∘ρ⇒≈id
  inv-isoʳ α⇒       = α⇒∘α⇐≈id
  inv-isoʳ α⇐       = α⇐∘α⇒≈id

  Coh-groupoid : Groupoid o o o
  Coh-groupoid = record
    { category   = MonoidalCategory.U Coh
    ; isGroupoid = record
      { _⁻¹ = inv
      ; iso = λ {A B f} → record { isoˡ = inv-isoˡ f ; isoʳ = inv-isoʳ f } }
    }

-- Faithfulness of ⟦-⟧
module Faithfulness (ℐ : MonoidalCategory 0ℓ 0ℓ 0ℓ)
                    ⦃ _ : DecEq (MonoidalCategory.Obj ℐ) ⦄ where
  open Coherence ℐ
  open CoherenceThm (MonoidalCategory.Obj ℐ)

  ⟦-⟧-faithful : Faithful ⟦-⟧
  ⟦-⟧-faithful {x = f} {y = g} _ = all-Comm f g
