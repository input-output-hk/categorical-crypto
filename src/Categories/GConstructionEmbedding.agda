{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Embedding a pair of base morphisms into the G construction, and the
-- two absorption laws that collapse the loop when one factor of a
-- G-composite is such an embedding:
--
--   absorbˡ : ⌜ u , v ⌝ ∘ g ≈ id ⊗ u ∘ g ∘ id ⊗ v
--   absorbʳ : f ∘ ⌜ p , q ⌝ ≈ q ⊗ id ∘ f ∘ p ⊗ id
--
-- They generalize `Categories.GConstruction`'s identity laws (the
-- `u = v = id` cases) and need no trace hypothesis beyond the four that
-- module already takes: `u` routes a loop input to an external output and
-- `v` an external input to a loop output, so both leave the trace by
-- `trace-∘ˡ`/`trace-∘ʳ`.  Every structural morphism of the Int/G
-- construction's monoidal structure is an embedding, so these are what
-- reduce its naturality and coherence obligations to base-level ones
-- (see `docs/ro-model-phase1.md`).
------------------------------------------------------------------------

module Categories.GConstructionEmbedding where

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Traced
open import Categories.GConstruction

open import Data.Product

import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U
import Categories.GConstructionEmbeddingCoherence as ECoh
import Categories.Morphism as Mor

module Embed {a b c} (C : Category a b c) (Monoidal : Monoidal C) (Traced : Traced Monoidal) where

  private
    module C where
      open Category C public
      open Traced Traced public
      open U.Shorthands Monoidal public
      open import Categories.Category.Monoidal.Reasoning Monoidal public
        using (⊗-distrib-over-∘; _⟩⊗⟨_)
      open import Categories.Morphism.Reasoning C public using (elimʳ; pullˡ)
      open BProps.Shorthands braided public

    Cˢ : SymmetricMonoidalCategory a b c
    Cˢ = record { U = C ; monoidal = Monoidal ; symmetric = C.symmetric }

    β : ∀ {P Q R : C.Obj} → (P C.⊗₀ Q) C.⊗₀ R C.⇒ (P C.⊗₀ R) C.⊗₀ Q
    β = C.α⇐ C.∘ C.id C.⊗₁ C.σ⇒ C.∘ C.α⇒

  -- `u` acts on the positive polarity, `v` on the negative one.  The
  -- G-identity at `(A⁺ , A⁻)` is `⌜ id , id ⌝`.
  ⌜_,_⌝ : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj} → A⁺ C.⇒ B⁺ → B⁻ C.⇒ A⁻ → A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺
  ⌜ u , v ⌝ = C.σ⇒ C.∘ u C.⊗₁ v

  private module MC = Mor C

  open C.HomReasoning

  ⌜⌝-resp-≈ : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj} {u u' : A⁺ C.⇒ B⁺} {v v' : B⁻ C.⇒ A⁻} →
              u C.≈ u' → v C.≈ v' → ⌜ u , v ⌝ C.≈ ⌜ u' , v' ⌝
  ⌜⌝-resp-≈ e₁ e₂ = refl⟩∘⟨ (e₁ C.⟩⊗⟨ e₂)

  module WithTrace
    (trace-resp-≈ : ∀ {X A B} {f g : A C.⊗₀ X C.⇒ B C.⊗₀ X} →
                    f C.≈ g → C.trace f C.≈ C.trace g)
    (trace-∘ˡ : ∀ {X A B B'} {g : B C.⇒ B'} {f : A C.⊗₀ X C.⇒ B C.⊗₀ X} →
                g C.∘ C.trace f C.≈ C.trace (g C.⊗₁ C.id C.∘ f))
    (trace-∘ʳ : ∀ {X A A' B} {f : A C.⊗₀ X C.⇒ B C.⊗₀ X} {h : A' C.⇒ A} →
                C.trace f C.∘ h C.≈ C.trace (f C.∘ h C.⊗₁ C.id))
    (trace-comm : ∀ {X Y A B} {f : (A C.⊗₀ X) C.⊗₀ Y C.⇒ (B C.⊗₀ X) C.⊗₀ Y} →
                  C.trace (C.trace f) C.≈ C.trace (C.trace (β C.∘ f C.∘ β)))
    where

    private
      G' : Category a b c
      G' = GConstruction C Monoidal Traced trace-resp-≈ trace-∘ˡ trace-∘ʳ trace-comm
      module G = Category G'
      module MG = Mor G'

    ⌜⌝-id : ∀ {A⁺ A⁻ : C.Obj} → ⌜ C.id {A⁺} , C.id {A⁻} ⌝ C.≈ G.id {A⁺ , A⁻}
    ⌜⌝-id = C.elimʳ C.⊗.identity

    absorbˡ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : C.Obj} {u : B⁺ C.⇒ D⁺} {v : D⁻ C.⇒ B⁻}
                {g : A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺} →
              G._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {D⁺ , D⁻} ⌜ u , v ⌝ g
                C.≈ C.id C.⊗₁ u C.∘ g C.∘ C.id C.⊗₁ v
    absorbˡ {A⁺} {A⁻} {B⁺} {B⁻} {D⁺} {D⁻} {u} {v} {g} =
      trace-resp-≈ (ECoh.L.Transport.WithGens.AL Cˢ A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ g u v)
      ○ ⟺ trace-∘ˡ
      ○ (refl⟩∘⟨ ⟺ trace-∘ʳ)
      ○ (refl⟩∘⟨ (G.identityˡ ⟩∘⟨refl))

    absorbʳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : C.Obj} {p : A⁺ C.⇒ B⁺} {q : B⁻ C.⇒ A⁻}
                {f : B⁺ C.⊗₀ D⁻ C.⇒ B⁻ C.⊗₀ D⁺} →
              G._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {D⁺ , D⁻} f ⌜ p , q ⌝
                C.≈ q C.⊗₁ C.id C.∘ f C.∘ p C.⊗₁ C.id
    absorbʳ {A⁺} {A⁻} {B⁺} {B⁻} {D⁺} {D⁻} {p} {q} {f} =
      trace-resp-≈ (ECoh.R.Transport.WithGens.AR Cˢ A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ f p q)
      ○ ⟺ trace-∘ˡ
      ○ (refl⟩∘⟨ ⟺ trace-∘ʳ)
      ○ (refl⟩∘⟨ (G.identityʳ ⟩∘⟨refl))

    -- Embedding is functorial: contravariant on the negative polarity.
    ⌜⌝-∘ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : C.Obj} {u : B⁺ C.⇒ D⁺} {v : D⁻ C.⇒ B⁻}
             {p : A⁺ C.⇒ B⁺} {q : B⁻ C.⇒ A⁻} →
           G._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {D⁺ , D⁻} ⌜ u , v ⌝ ⌜ p , q ⌝
             C.≈ ⌜ u C.∘ p , q C.∘ v ⌝
    ⌜⌝-∘ {A⁻ = A⁻} {u = u} {v} {p} {q} = absorbˡ ○ (begin
      C.id C.⊗₁ u C.∘ (C.σ⇒ C.∘ p C.⊗₁ q) C.∘ C.id C.⊗₁ v
        ≈⟨ refl⟩∘⟨ C.assoc ⟩
      C.id C.⊗₁ u C.∘ C.σ⇒ C.∘ p C.⊗₁ q C.∘ C.id C.⊗₁ v
        ≈⟨ C.pullˡ (⟺ (C.braiding.⇒.commute (u , C.id {A⁻}))) ⟩
      (C.σ⇒ C.∘ u C.⊗₁ C.id) C.∘ p C.⊗₁ q C.∘ C.id C.⊗₁ v
        ≈⟨ C.assoc ⟩
      C.σ⇒ C.∘ u C.⊗₁ C.id C.∘ p C.⊗₁ q C.∘ C.id C.⊗₁ v
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ⟺ C.⊗-distrib-over-∘) ⟩
      C.σ⇒ C.∘ u C.⊗₁ C.id C.∘ (p C.∘ C.id) C.⊗₁ (q C.∘ v)
        ≈⟨ refl⟩∘⟨ ⟺ C.⊗-distrib-over-∘ ⟩
      C.σ⇒ C.∘ (u C.∘ p C.∘ C.id) C.⊗₁ (C.id C.∘ q C.∘ v)
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ C.identityʳ) C.⟩⊗⟨ C.identityˡ ⟩
      C.σ⇒ C.∘ (u C.∘ p) C.⊗₁ (q C.∘ v)
      ∎)

    -- Hence a pair of base isos embeds as a G-iso, which is what makes every
    -- structural morphism of the Int/G construction invertible.
    ⌜⌝-≅ : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj} → MC._≅_ A⁺ B⁺ → MC._≅_ B⁻ A⁻ → MG._≅_ (A⁺ , A⁻) (B⁺ , B⁻)
    ⌜⌝-≅ u v = record
      { from = ⌜ u.from , v.from ⌝
      ; to   = ⌜ u.to , v.to ⌝
      ; iso  = record
        { isoˡ = ⌜⌝-∘ ○ ⌜⌝-resp-≈ u.isoˡ v.isoʳ ○ ⌜⌝-id
        ; isoʳ = ⌜⌝-∘ ○ ⌜⌝-resp-≈ u.isoʳ v.isoˡ ○ ⌜⌝-id
        }
      }
      where module u = MC._≅_ u
            module v = MC._≅_ v

    -- The structural isos of the pairwise tensor `(A⁺,A⁻) ⊗ (B⁺,B⁻) =
    -- (A⁺⊗B⁺ , A⁻⊗B⁻)` with unit `(I,I)`: each polarity gets the base iso, the
    -- negative one reversed.
    unitorˡᴳ : ∀ {A⁺ A⁻ : C.Obj} → MG._≅_ (C.unit C.⊗₀ A⁺ , C.unit C.⊗₀ A⁻) (A⁺ , A⁻)
    unitorˡᴳ = ⌜⌝-≅ C.unitorˡ (MC.≅.sym C.unitorˡ)

    unitorʳᴳ : ∀ {A⁺ A⁻ : C.Obj} → MG._≅_ (A⁺ C.⊗₀ C.unit , A⁻ C.⊗₀ C.unit) (A⁺ , A⁻)
    unitorʳᴳ = ⌜⌝-≅ C.unitorʳ (MC.≅.sym C.unitorʳ)

    associatorᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : C.Obj} →
                  MG._≅_ ((A⁺ C.⊗₀ B⁺) C.⊗₀ D⁺ , (A⁻ C.⊗₀ B⁻) C.⊗₀ D⁻)
                         (A⁺ C.⊗₀ (B⁺ C.⊗₀ D⁺) , A⁻ C.⊗₀ (B⁻ C.⊗₀ D⁻))
    associatorᴳ = ⌜⌝-≅ C.associator (MC.≅.sym C.associator)
