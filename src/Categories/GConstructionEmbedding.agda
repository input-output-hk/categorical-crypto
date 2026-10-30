{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Embedding a pair of base morphisms into the G construction, and the
-- two absorption laws: composing with an embedding collapses the loop,
-- since `u` routes a loop input to an external output and `v` an
-- external input to a loop output, so both leave the trace by
-- `trace-∘ˡ`/`trace-∘ʳ`.  Every structural morphism of the monoidal
-- structure is an embedding, so these reduce its naturality and
-- coherence obligations to base-level ones.
------------------------------------------------------------------------

module Categories.GConstructionEmbedding where

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Product
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Traced.Ext as TE
open import Categories.Functor using (Functor)
open import Categories.Functor.Properties
open import Categories.GConstruction

open import Data.Product

import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U
import Categories.GConstructionEmbeddingCoherence as ECoh
import Categories.GConstructionTrace as GT
import Categories.Morphism as Mor

module Embed {a b c} (C : Category a b c) (Monoidal : Monoidal C) (Traced : Traced Monoidal) where

  open Category C
  open Traced Traced
  open U.Shorthands Monoidal
  open import Categories.Category.Monoidal.Reasoning Monoidal
    using (⊗-distrib-over-∘; _⟩⊗⟨_)
  open import Categories.Morphism.Reasoning C using (elimʳ; pullˡ)
  open BProps.Shorthands braided
  open GT C Monoidal Traced using (Cˢ)

  open HomReasoning

  ⌜_,_⌝ : ∀ {A⁺ A⁻ B⁺ B⁻ : Obj} → A⁺ ⇒ B⁺ → B⁻ ⇒ A⁻ → A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺
  ⌜ u , v ⌝ = σ⇒ ∘ u ⊗₁ v

  private module MC = Mor C

  ⌜⌝-resp-≈ : ∀ {A⁺ A⁻ B⁺ B⁻ : Obj} {u u' : A⁺ ⇒ B⁺} {v v' : B⁻ ⇒ A⁻} →
              u ≈ u' → v ≈ v' → ⌜ u , v ⌝ ≈ ⌜ u' , v' ⌝
  ⌜⌝-resp-≈ e₁ e₂ = refl⟩∘⟨ (e₁ ⟩⊗⟨ e₂)

  module WithTrace (L : TE.Laws Traced) where

    open TE.Laws L

    private
      G' : Category a b c
      G' = GConstruction C Monoidal Traced L
      module G = Category G'
      module MG = Mor G'

    ⌜⌝-id : ∀ {A⁺ A⁻ : Obj} → ⌜ id , id ⌝ ≈ G.id {A⁺ , A⁻}
    ⌜⌝-id = elimʳ ⊗.identity

    opaque
      unfolding composeᴳ

      absorbˡ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : Obj} {u : B⁺ ⇒ D⁺} {v : D⁻ ⇒ B⁻}
                  {g : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} →
                G._∘_ ⌜ u , v ⌝ g
                  ≈ id ⊗₁ u ∘ g ∘ id ⊗₁ v
      absorbˡ {A⁺} {A⁻} {B⁺} {B⁻} {D⁺} {D⁻} {u} {v} {g} =
        trace-resp-≈ (ECoh.L.Transport.WithGens.AL Cˢ A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ g u v)
        ○ ⟺ trace-∘ˡ
        ○ (refl⟩∘⟨ ⟺ trace-∘ʳ)
        ○ (refl⟩∘⟨ (G.identityˡ ⟩∘⟨refl))

      absorbʳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : Obj} {p : A⁺ ⇒ B⁺} {q : B⁻ ⇒ A⁻}
                  {f : B⁺ ⊗₀ D⁻ ⇒ B⁻ ⊗₀ D⁺} →
                G._∘_ f ⌜ p , q ⌝
                  ≈ q ⊗₁ id ∘ f ∘ p ⊗₁ id
      absorbʳ {A⁺} {A⁻} {B⁺} {B⁻} {D⁺} {D⁻} {p} {q} {f} =
        trace-resp-≈ (ECoh.R.Transport.WithGens.AR Cˢ A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ f p q)
        ○ ⟺ trace-∘ˡ
        ○ (refl⟩∘⟨ ⟺ trace-∘ʳ)
        ○ (refl⟩∘⟨ (G.identityʳ ⟩∘⟨refl))

    ⌜⌝-∘ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : Obj} {u : B⁺ ⇒ D⁺} {v : D⁻ ⇒ B⁻}
             {p : A⁺ ⇒ B⁺} {q : B⁻ ⇒ A⁻} →
           G._∘_ ⌜ u , v ⌝ ⌜ p , q ⌝
             ≈ ⌜ u ∘ p , q ∘ v ⌝
    ⌜⌝-∘ {A⁻ = A⁻} {u = u} {v} {p} {q} = absorbˡ ○ (begin
      id ⊗₁ u ∘ (σ⇒ ∘ p ⊗₁ q) ∘ id ⊗₁ v
        ≈⟨ refl⟩∘⟨ assoc ⟩
      id ⊗₁ u ∘ σ⇒ ∘ p ⊗₁ q ∘ id ⊗₁ v
        ≈⟨ pullˡ (⟺ (braiding.⇒.commute (u , id))) ⟩
      (σ⇒ ∘ u ⊗₁ id) ∘ p ⊗₁ q ∘ id ⊗₁ v
        ≈⟨ assoc ⟩
      σ⇒ ∘ u ⊗₁ id ∘ p ⊗₁ q ∘ id ⊗₁ v
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ⟺ ⊗-distrib-over-∘) ⟩
      σ⇒ ∘ u ⊗₁ id ∘ (p ∘ id) ⊗₁ (q ∘ v)
        ≈⟨ refl⟩∘⟨ ⟺ ⊗-distrib-over-∘ ⟩
      σ⇒ ∘ (u ∘ p ∘ id) ⊗₁ (id ∘ q ∘ v)
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ identityʳ) ⟩⊗⟨ identityˡ ⟩
      σ⇒ ∘ (u ∘ p) ⊗₁ (q ∘ v)
      ∎)

    embed : Functor (Product C op) G'
    embed = record
      { F₀ = λ A → A
      ; F₁ = λ (u , v) → ⌜ u , v ⌝
      ; identity = ⌜⌝-id
      ; homomorphism = ⟺ ⌜⌝-∘
      ; F-resp-≈ = λ (e₁ , e₂) → ⌜⌝-resp-≈ e₁ e₂
      }

    ⌜⌝-≅ : ∀ {A⁺ A⁻ B⁺ B⁻ : Obj} → MC._≅_ A⁺ B⁺ → MC._≅_ B⁻ A⁻ → MG._≅_ (A⁺ , A⁻) (B⁺ , B⁻)
    ⌜⌝-≅ u v = [ embed ]-resp-≅ record
      { from = u.from , v.from ; to = u.to , v.to
      ; iso = record { isoˡ = u.isoˡ , v.isoʳ ; isoʳ = u.isoʳ , v.isoˡ } }
      where module u = MC._≅_ u
            module v = MC._≅_ v

    unitorˡᴳ : ∀ {A⁺ A⁻ : Obj} → MG._≅_ (unit ⊗₀ A⁺ , unit ⊗₀ A⁻) (A⁺ , A⁻)
    unitorˡᴳ = ⌜⌝-≅ unitorˡ (MC.≅.sym unitorˡ)

    unitorʳᴳ : ∀ {A⁺ A⁻ : Obj} → MG._≅_ (A⁺ ⊗₀ unit , A⁻ ⊗₀ unit) (A⁺ , A⁻)
    unitorʳᴳ = ⌜⌝-≅ unitorʳ (MC.≅.sym unitorʳ)

    associatorᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : Obj} →
                  MG._≅_ ((A⁺ ⊗₀ B⁺) ⊗₀ D⁺ , (A⁻ ⊗₀ B⁻) ⊗₀ D⁻)
                         (A⁺ ⊗₀ (B⁺ ⊗₀ D⁺) , A⁻ ⊗₀ (B⁻ ⊗₀ D⁻))
    associatorᴳ = ⌜⌝-≅ associator (MC.≅.sym associator)
