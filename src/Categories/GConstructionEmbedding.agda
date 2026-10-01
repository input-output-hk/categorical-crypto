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
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Traced.Ext as TE
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

  ⌜_,_⌝ : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj} → A⁺ C.⇒ B⁺ → B⁻ C.⇒ A⁻ → A⁺ C.⊗₀ B⁻ C.⇒ A⁻ C.⊗₀ B⁺
  ⌜ u , v ⌝ = C.σ⇒ C.∘ u C.⊗₁ v

  private module MC = Mor C

  open C.HomReasoning

  ⌜⌝-resp-≈ : ∀ {A⁺ A⁻ B⁺ B⁻ : C.Obj} {u u' : A⁺ C.⇒ B⁺} {v v' : B⁻ C.⇒ A⁻} →
              u C.≈ u' → v C.≈ v' → ⌜ u , v ⌝ C.≈ ⌜ u' , v' ⌝
  ⌜⌝-resp-≈ e₁ e₂ = refl⟩∘⟨ (e₁ C.⟩⊗⟨ e₂)

  module WithTrace (L : TE.Laws Traced) where

    open TE.Laws L

    private
      G' : Category a b c
      G' = GConstruction C Monoidal Traced L
      module G = Category G'
      module MG = Mor G'

    ⌜⌝-id : ∀ {A⁺ A⁻ : C.Obj} → ⌜ C.id {A⁺} , C.id {A⁻} ⌝ C.≈ G.id {A⁺ , A⁻}
    ⌜⌝-id = C.elimʳ C.⊗.identity

    opaque
      unfolding composeᴳ

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

    unitorˡᴳ : ∀ {A⁺ A⁻ : C.Obj} → MG._≅_ (C.unit C.⊗₀ A⁺ , C.unit C.⊗₀ A⁻) (A⁺ , A⁻)
    unitorˡᴳ = ⌜⌝-≅ C.unitorˡ (MC.≅.sym C.unitorˡ)

    unitorʳᴳ : ∀ {A⁺ A⁻ : C.Obj} → MG._≅_ (A⁺ C.⊗₀ C.unit , A⁻ C.⊗₀ C.unit) (A⁺ , A⁻)
    unitorʳᴳ = ⌜⌝-≅ C.unitorʳ (MC.≅.sym C.unitorʳ)

    associatorᴳ : ∀ {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : C.Obj} →
                  MG._≅_ ((A⁺ C.⊗₀ B⁺) C.⊗₀ D⁺ , (A⁻ C.⊗₀ B⁻) C.⊗₀ D⁻)
                         (A⁺ C.⊗₀ (B⁺ C.⊗₀ D⁺) , A⁻ C.⊗₀ (B⁻ C.⊗₀ D⁻))
    associatorᴳ = ⌜⌝-≅ C.associator (MC.≅.sym C.associator)
