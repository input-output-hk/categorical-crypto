{-# OPTIONS --safe --without-K #-}

-- Coh(ℐ): the monoidal category of coherence isomorphisms of a monoidal
-- category ℐ. It is the free monoidal category over `Ob ℐ` with NO morphism
-- generators, so every hom is a structural coherence iso.
--
-- The interpretation functor ⟦-⟧ : Coh(ℐ) → ℐ is faithful.

module Categories.CoherenceIsos where

open import Level using (Level; 0ℓ)
open import Data.Empty using (⊥)

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Groupoid using (Groupoid)
open import Categories.Category.Monoidal using (MonoidalCategory)
import Categories.Category.Monoidal.Reasoning as MonR
open import Categories.Coherence.Monoidal.MacLane using (module CoherenceThm)
open import Categories.FreeMonoidal
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal using (MonoidalFunctor)
open import Categories.Functor.Properties using (Faithful)
import Categories.Morphism.Reasoning as MR

open import Class.DecEq using (DecEq)

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
  open FM public using (Var)

  inv : ∀ {A B} → FM.HomTerm A B → FM.HomTerm B A
  inv (FM.var ())
  inv FM.id       = FM.id
  inv (g FM.∘ f)  = inv f FM.∘ inv g
  inv (f FM.⊗₁ g) = inv f FM.⊗₁ inv g
  inv FM.λ⇒       = FM.λ⇐
  inv FM.λ⇐       = FM.λ⇒
  inv FM.ρ⇒       = FM.ρ⇐
  inv FM.ρ⇐       = FM.ρ⇒
  inv FM.α⇒       = FM.α⇐
  inv FM.α⇐       = FM.α⇒

  open MonR (MonoidalCategory.monoidal Coh)
  open MR FM.FreeMonoidal

  inv-isoˡ : ∀ {A B} (f : FM.HomTerm A B) → FM.FreeMonoidal [ inv f FM.∘ f ≈ FM.id ]
  inv-isoˡ (FM.var ())
  inv-isoˡ FM.id       = FM.idˡ
  inv-isoˡ (g FM.∘ f)  = cancelInner (inv-isoˡ g) ○ inv-isoˡ f
  inv-isoˡ (f FM.⊗₁ g) = ⟺ FM.⊗-∘-dist ○ (inv-isoˡ f ⟩⊗⟨ inv-isoˡ g) ○ FM.id⊗id≈id
  inv-isoˡ FM.λ⇒       = FM.λ⇐∘λ⇒≈id
  inv-isoˡ FM.λ⇐       = FM.λ⇒∘λ⇐≈id
  inv-isoˡ FM.ρ⇒       = FM.ρ⇐∘ρ⇒≈id
  inv-isoˡ FM.ρ⇐       = FM.ρ⇒∘ρ⇐≈id
  inv-isoˡ FM.α⇒       = FM.α⇐∘α⇒≈id
  inv-isoˡ FM.α⇐       = FM.α⇒∘α⇐≈id

  inv-isoʳ : ∀ {A B} (f : FM.HomTerm A B) → FM.FreeMonoidal [ f FM.∘ inv f ≈ FM.id ]
  inv-isoʳ (FM.var ())
  inv-isoʳ FM.id       = FM.idˡ
  inv-isoʳ (g FM.∘ f)  = cancelInner (inv-isoʳ f) ○ inv-isoʳ g
  inv-isoʳ (f FM.⊗₁ g) = ⟺ FM.⊗-∘-dist ○ (inv-isoʳ f ⟩⊗⟨ inv-isoʳ g) ○ FM.id⊗id≈id
  inv-isoʳ FM.λ⇒       = FM.λ⇒∘λ⇐≈id
  inv-isoʳ FM.λ⇐       = FM.λ⇐∘λ⇒≈id
  inv-isoʳ FM.ρ⇒       = FM.ρ⇒∘ρ⇐≈id
  inv-isoʳ FM.ρ⇐       = FM.ρ⇐∘ρ⇒≈id
  inv-isoʳ FM.α⇒       = FM.α⇒∘α⇐≈id
  inv-isoʳ FM.α⇐       = FM.α⇐∘α⇒≈id

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
  open Coherence ℐ using (⟦-⟧)
  open CoherenceThm (MonoidalCategory.Obj ℐ) using (all-Comm)

  ⟦-⟧-faithful : Faithful ⟦-⟧
  ⟦-⟧-faithful {x = f} {y = g} _ = all-Comm f g
