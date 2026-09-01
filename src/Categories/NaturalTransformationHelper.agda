{-# OPTIONS --safe --without-K #-}

module Categories.NaturalTransformationHelper where

open import Level

open import Categories.Category
open import Categories.Category.Product
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.Functor.Bifunctor.Properties
open import Categories.Tactic.Category

open import Data.Product

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

module _ (F G : Bifunctor C D E) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G

  open Category E
  open HomReasoning

  -- The pointwise naturality square of `pointwise-iso` (the `from`-component
  -- family `η` is natural), assembled for a bifunctor from naturality in each
  -- argument separately via the `[ _ ]-decompose₁` interchange.
  natural-components : (η : ∀ X → E [ F.F₀ X , G.F₀ X ])
                     → (∀ d {X Y} (f : C [ X , Y ])
                          → η (Y , d) ∘ F.F₁ (f , D.id) ≈ G.F₁ (f , D.id) ∘ η (X , d))
                     → (∀ c {X Y} (f : D [ X , Y ])
                          → η (c , Y) ∘ F.F₁ (C.id , f) ≈ G.F₁ (C.id , f) ∘ η (c , X))
                     → ∀ {X Y} (f : Product C D [ X , Y ])
                          → η Y ∘ F.F₁ f ≈ G.F₁ f ∘ η X
  natural-components η natural₁ natural₂ {X} {Y} (f₁ , f₂) = begin
    η Y ∘ F.F₁ (f₁ , f₂)
      ≈⟨ refl⟩∘⟨ [ F ]-decompose₁ ⟩
    η Y ∘ F.F₁ (f₁ , D.id) ∘ F.F₁ (C.id , f₂)
      ≈⟨ solve E ⟩
    (η Y ∘ F.F₁ (f₁ , D.id)) ∘ F.F₁ (C.id , f₂)
      ≈⟨ natural₁ _ f₁ ⟩∘⟨refl ⟩
    (G.F₁ (f₁ , D.id) ∘ η _) ∘ F.F₁ (C.id , f₂)
      ≈⟨ solve E ⟩
    G.F₁ (f₁ , D.id) ∘ η _ ∘ F.F₁ (C.id , f₂)
      ≈⟨ refl⟩∘⟨ natural₂ _ f₂ ⟩
    G.F₁ (f₁ , D.id) ∘ G.F₁ (C.id , f₂) ∘ η X
      ≈⟨ solve E ⟩
    (G.F₁ (f₁ , D.id) ∘ G.F₁ (C.id , f₂)) ∘ η X
      ≈⟨ [ G ]-decompose₁ ⟩∘⟨refl ⟨
    G.F₁ (f₁ , f₂) ∘ η X ∎
