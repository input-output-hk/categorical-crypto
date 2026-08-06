{-# OPTIONS --safe --without-K #-}

-- Locally graded categories over a monoidal ℐ: the elementary
-- unpacking of a category enriched in presheaves on ℐ under Day
-- convolution.

module Categories.LocallyGraded where

open import Level
open import Relation.Binary

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Utilities as Utilities
open import Categories.Functor using (Functor)

record LocallyGradedCategory {o ℓ e : Level} (ℐ : MonoidalCategory o ℓ e)
    (o′ ℓ′ e′ : Level) : Set (o ⊔ ℓ ⊔ e ⊔ suc (o′ ⊔ ℓ′ ⊔ e′)) where
  private module ℐ = MonoidalCategory ℐ
  open ℐ using (_⊗₀_; _⊗₁_)
  open Utilities.Shorthands ℐ.monoidal

  infixr 9 _∙_
  infix  4 _≈_

  field
    Obj : Set o′
    Hom : ℐ.Obj → Obj → Obj → Set ℓ′
    _≈_ : ∀ {X A B} → Hom X A B → Hom X A B → Set e′
    equiv : ∀ {X A B} → IsEquivalence (_≈_ {X} {A} {B})

    -- reindexing along grade morphisms: each hom family is a functor ℐ → Set
    sub[_] : ∀ {X Y A B} → X ℐ.⇒ Y → Hom X A B → Hom Y A B
    sub-identity : ∀ {X A B} {f : Hom X A B} → sub[ ℐ.id ] f ≈ f
    sub-homomorphism : ∀ {X Y Z A B} {a : X ℐ.⇒ Y} {b : Y ℐ.⇒ Z}
                       {f : Hom X A B} → sub[ b ℐ.∘ a ] f ≈ sub[ b ] (sub[ a ] f)
    sub-resp-≈ : ∀ {X Y A B} {a b : X ℐ.⇒ Y} {f g : Hom X A B}
               → a ℐ.≈ b → f ≈ g → sub[ a ] f ≈ sub[ b ] g

    id : ∀ {A} → Hom ℐ.unit A A
    _∙_ : ∀ {X Y A B C} → Hom Y B C → Hom X A B → Hom (X ⊗₀ Y) A C
    ∙-resp-≈ : ∀ {X Y A B C} {h h′ : Hom Y B C} {f f′ : Hom X A B}
             → h ≈ h′ → f ≈ f′ → h ∙ f ≈ h′ ∙ f′

    -- unit and associativity laws, up to reindexing by ℐ's structure isos
    identityˡ : ∀ {X A B} {f : Hom X A B} → sub[ ρ⇒ ] (id ∙ f) ≈ f
    identityʳ : ∀ {X A B} {f : Hom X A B} → sub[ λ⇒ ] (f ∙ id) ≈ f
    assoc : ∀ {X P Q A B C D} {h : Hom Q C D} {g : Hom P B C} {f : Hom X A B}
          → (h ∙ g) ∙ f ≈ sub[ α⇒ ] (h ∙ (g ∙ f))

    -- enrichment naturality: composition is a map of ℐ-presheaves
    interchange : ∀ {X X′ P P′ A B C} {a : X ℐ.⇒ X′} {b : P ℐ.⇒ P′}
                  {h : Hom P B C} {f : Hom X A B}
                → sub[ b ] h ∙ sub[ a ] f ≈ sub[ a ⊗₁ b ] (h ∙ f)

  module Equiv {X A B} = IsEquivalence (equiv {X} {A} {B})

record LocallyGradedFunctor {o ℓ e o₁ ℓ₁ e₁ o₂ ℓ₂ e₂} {ℐ : MonoidalCategory o ℓ e}
    (L : LocallyGradedCategory ℐ o₁ ℓ₁ e₁) (M : LocallyGradedCategory ℐ o₂ ℓ₂ e₂)
    : Set (o ⊔ ℓ ⊔ o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₂ ⊔ ℓ₂ ⊔ e₂) where
  private
    module ℐ = MonoidalCategory ℐ
    module L = LocallyGradedCategory L
    module M = LocallyGradedCategory M

  field
    F₀ : L.Obj → M.Obj
    F₁ : ∀ {X A B} → L.Hom X A B → M.Hom X (F₀ A) (F₀ B)
    F-resp-≈ : ∀ {X A B} {f g : L.Hom X A B} → f L.≈ g → F₁ f M.≈ F₁ g
    F-sub : ∀ {X Y A B} {a : X ℐ.⇒ Y} {f : L.Hom X A B}
          → F₁ (L.sub[ a ] f) M.≈ M.sub[ a ] (F₁ f)
    identity : ∀ {A} → F₁ (L.id {A}) M.≈ M.id
    homomorphism : ∀ {X Y A B C} {g : L.Hom Y B C} {f : L.Hom X A B}
                 → F₁ (g L.∙ f) M.≈ F₁ g M.∙ F₁ f

module _ {o ℓ e o′ ℓ′ e′} {ℐ : MonoidalCategory o ℓ e}
  (L : LocallyGradedCategory ℐ o′ ℓ′ e′) where

  private
    module L = LocallyGradedCategory L
    module ℐ = MonoidalCategory ℐ

  -- the `sub-*` laws, packaged: each hom family is a functor of the grade
  HomF : (A B : L.Obj) → Functor ℐ.U (Setoids ℓ′ e′)
  HomF A B = record
    { F₀           = λ X → record
      { Carrier = L.Hom X A B ; _≈_ = L._≈_ ; isEquivalence = L.equiv }
    ; F₁           = λ ψ → record { to = L.sub[ ψ ] ; cong = L.sub-resp-≈ ℐ.Equiv.refl }
    ; identity     = L.sub-identity
    ; homomorphism = L.sub-homomorphism
    ; F-resp-≈     = λ ψ≈ → L.sub-resp-≈ ψ≈ L.Equiv.refl
    }
