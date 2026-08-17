{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Extensions to `Categories.Functor.Monoidal.Properties`.
------------------------------------------------------------------------

open import Data.Product
open import Level

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Functor.Monoidal
import Categories.Morphism.Reasoning as MR

import Categories.Morphism.Reasoning.Ext as MRExt

module Categories.Functor.Monoidal.Properties.Ext where

-- The oplax (comonoidal) structure that a strong monoidal functor carries:
module Oplax {o ℓ e o′ ℓ′ e′ : Level}
             {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′}
             (F : StrongMonoidalFunctor C D) where

  private
    module C  = MonoidalCategory C
    module CS = MonoidalUtilities.Shorthands C.monoidal
    module F  = StrongMonoidalFunctor F

  open F hiding (F)
  open MonoidalCategory D
  open MonoidalReasoning monoidal
  open MonoidalUtilities.Shorthands monoidal
  open MR U
  open MRExt U

  δ : ∀ {X Y} → F₀ (X C.⊗₀ Y) ⇒ F₀ X ⊗₀ F₀ Y
  δ {X} {Y} = ⊗-homo.⇐.η (X , Y)

  ψ : ∀ {X Y} → F₀ X ⊗₀ F₀ Y ⇒ F₀ (X C.⊗₀ Y)
  ψ {X} {Y} = ⊗-homo.⇒.η (X , Y)

  δψ : ∀ {X Y} → δ {X} {Y} ∘ ψ ≈ id
  δψ = ⊗-homo.iso.isoˡ _

  ψδ : ∀ {X Y} → ψ {X} {Y} ∘ δ ≈ id
  ψδ = ⊗-homo.iso.isoʳ _

  δ-commute : ∀ {X X′ Y Y′} (f : X C.⇒ X′) (g : Y C.⇒ Y′) →
              δ ∘ F₁ (f C.⊗₁ g) ≈ F₁ f ⊗₁ F₁ g ∘ δ
  δ-commute f g = ⊗-homo.⇐.commute (f , g)

  δ-commuteˡ : ∀ {X Y Y′} (g : Y C.⇒ Y′) → δ {X} {Y′} ∘ F₁ (C.id C.⊗₁ g)
                                         ≈ id ⊗₁ F₁ g ∘ δ
  δ-commuteˡ g = δ-commute C.id g ○ ((identity ⟩⊗⟨refl) ⟩∘⟨refl)

  δ-commuteʳ : ∀ {X X′ Y} (f : X C.⇒ X′) → δ {X′} {Y} ∘ F₁ (f C.⊗₁ C.id)
                                         ≈ F₁ f ⊗₁ id ∘ δ
  δ-commuteʳ f = δ-commute f C.id ○ ((refl⟩⊗⟨ identity) ⟩∘⟨refl)

  private
    F-cancel : ∀ {X Y} {f : X C.⇒ Y} {g : Y C.⇒ X} → f C.∘ g C.≈ C.id → F₁ f ∘ F₁ g ≈ id
    F-cancel eq = ⟺ homomorphism ○ F-resp-≈ eq ○ identity

    ⊗-cancel₁ : ∀ {A B W} {f : A ⇒ B} {g : B ⇒ A} → f ∘ g ≈ id → f ⊗₁ id {W} ∘ g ⊗₁ id ≈ id
    ⊗-cancel₁ eq = merge₁ˡ ○ eq ⟩⊗⟨refl ○ ⊗.identity

    ⊗-cancel₂ : ∀ {A B W} {f : A ⇒ B} {g : B ⇒ A} → f ∘ g ≈ id → id {W} ⊗₁ f ∘ id ⊗₁ g ≈ id
    ⊗-cancel₂ eq = merge₂ʳ ○ refl⟩⊗⟨ eq ○ ⊗.identity

  δ-assoc : ∀ {X Y Z} → δ {X} ⊗₁ id ∘ δ ∘ F₁ CS.α⇐
                      ≈ α⇐ ∘ id ⊗₁ δ {Y} {Z} ∘ δ
  δ-assoc = inv-resp
    (sym-assoc ⟩∘⟨refl ○ cancelInner (F-cancel C.associator.isoˡ) ○ cancelInner δψ ○ ⊗-cancel₁ δψ)
    (sym-assoc ⟩∘⟨refl ○ cancelInner associator.isoʳ ○ cancelInner (⊗-cancel₂ ψδ) ○ ψδ)
    associativity

  -- `δ-assoc` with the leading `δ ⊗₁ id` cancelled away and the trailing `δ` exposed
  δ-assoc′ : ∀ {X Y Z} → δ {X C.⊗₀ Y} ∘ F₁ (CS.α⇐ {X} {Y} {Z})
           ≈ (ψ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ δ) ∘ δ
  δ-assoc′ = introˡ (⊗-cancel₁ ψδ) ○ assoc ○ (refl⟩∘⟨ δ-assoc) ○ assoc²εβ

  δ-unitorˡ : ∀ {X} → δ {C.unit} {X} ∘ F₁ CS.λ⇐ ≈ ε.from ⊗₁ id ∘ λ⇐
  δ-unitorˡ = inv-resp
    (cancelInner (F-cancel C.unitorˡ.isoˡ) ○ δψ)
    (cancelInner (⊗-cancel₁ ε.isoˡ) ○ unitorˡ.isoʳ)
    (insertʳ (⊗-cancel₁ ε.isoʳ) ○ assoc ⟩∘⟨refl ○ unitaryˡ ⟩∘⟨refl)

  δ-unitorʳ : ∀ {X} → δ {X} ∘ F₁ CS.ρ⇐ ≈ id ⊗₁ ε.from ∘ ρ⇐
  δ-unitorʳ = inv-resp
    (cancelInner (F-cancel C.unitorʳ.isoˡ) ○ δψ)
    (cancelInner (⊗-cancel₂ ε.isoˡ) ○ unitorʳ.isoʳ)
    (insertʳ (⊗-cancel₂ ε.isoʳ) ○ assoc ⟩∘⟨refl ○ unitaryʳ ⟩∘⟨refl)
