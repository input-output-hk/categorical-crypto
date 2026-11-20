{-# OPTIONS --safe --without-K #-}

-- Pushing a monoidal structure along an identity on objects functor

open import Categories.Category.Core
open import Categories.Category.Monoidal.Core
open import Categories.Category.Unbundled.Properties
open import Categories.Functor.Bifunctor
open import Categories.Functor.IdentityOnObjects
open import Categories.Functor.Properties
import Categories.Category.Unbundled as Unbundled

open import Data.Product
open import Level

module Categories.Category.Monoidal.Construction.Transport
  {o ℓ e ℓ′ e′} {Obj : Set o}
  (C : Unbundled.Category Obj ℓ e) (D : Unbundled.Category Obj ℓ′ e′)
  (M : Monoidal (pack′ C)) (F : IdentityOnObjects C D) where

private
  module C = Category (pack′ C)
  module D = Category (pack′ D)
  module M = Monoidal M
  module F = IdentityOnObjects F

open D using (_⇒_; _≈_; _∘_; id)
open D.Equiv
open D.HomReasoning

private variable A B X Y Z W : Obj

record Transport : Set (o ⊔ ℓ ⊔ e ⊔ ℓ′ ⊔ e′) where
  infixr 10 _⊗₁_

  field
    _⊗₁_ : A ⇒ B → X ⇒ Y → A M.⊗₀ X ⇒ B M.⊗₀ Y
    ⊗-identity : id {A} ⊗₁ id {B} ≈ id
    ⊗-homomorphism : {f : A ⇒ B} {g : B ⇒ X} {h : Y ⇒ Z} {i : Z ⇒ W} →
                       (g ∘ f) ⊗₁ (i ∘ h) ≈ g ⊗₁ i ∘ f ⊗₁ h
    ⊗-resp-≈ : {f f′ : A ⇒ B} {g g′ : X ⇒ Y} →
                 f ≈ f′ → g ≈ g′ → f ⊗₁ g ≈ f′ ⊗₁ g′
    ⊗-compatible : (f : A C.⇒ B) (g : X C.⇒ Y) →
                     F.F₁ f ⊗₁ F.F₁ g ≈ F.F₁ (f M.⊗₁ g)
    unitorˡ-commute : {f : A ⇒ B} →
                       F.F₁ M.unitorˡ.from ∘ id ⊗₁ f ≈ f ∘ F.F₁ M.unitorˡ.from
    unitorʳ-commute : {f : A ⇒ B} →
                       F.F₁ M.unitorʳ.from ∘ f ⊗₁ id ≈ f ∘ F.F₁ M.unitorʳ.from
    assoc-commute : {f : A ⇒ B} {g : X ⇒ Y} {h : Z ⇒ W} →
                     F.F₁ M.associator.from ∘ (f ⊗₁ g) ⊗₁ h
                     ≈ f ⊗₁ (g ⊗₁ h) ∘ F.F₁ M.associator.from

  ⊗ : Bifunctor (pack′ D) (pack′ D) (pack′ D)
  ⊗ = record
    { F₀ = λ (A , B) → A M.⊗₀ B
    ; F₁ = λ (f , g) → f ⊗₁ g
    ; identity = ⊗-identity
    ; homomorphism = ⊗-homomorphism
    ; F-resp-≈ = λ (eq₁ , eq₂) → ⊗-resp-≈ eq₁ eq₂
    }

  ⊗-compatibleˡ : (f : A C.⇒ B) → id {X} ⊗₁ F.F₁ f ≈ F.F₁ (C.id M.⊗₁ f)
  ⊗-compatibleˡ f = ⊗-resp-≈ (⟺ F.identity) refl ○ ⊗-compatible C.id f

  ⊗-compatibleʳ : (f : A C.⇒ B) → F.F₁ f ⊗₁ id {X} ≈ F.F₁ (f M.⊗₁ C.id)
  ⊗-compatibleʳ f = ⊗-resp-≈ refl (⟺ F.identity) ○ ⊗-compatible f C.id

  opaque
    triangle : id {A} ⊗₁ F.F₁ (M.unitorˡ.from {B}) ∘ F.F₁ M.associator.from
               ≈ F.F₁ M.unitorʳ.from ⊗₁ id
    triangle = ⊗-compatibleˡ M.unitorˡ.from ⟩∘⟨refl
             ○ [ IOO⇒Functor F ]-resp-∘ M.triangle
             ○ ⟺ (⊗-compatibleʳ M.unitorʳ.from)

    pentagon : id ⊗₁ F.F₁ (M.associator.from {B} {X} {Y}) ∘ F.F₁ M.associator.from
               ∘ F.F₁ (M.associator.from {A} {B} {X}) ⊗₁ id
               ≈ F.F₁ M.associator.from ∘ F.F₁ M.associator.from
    pentagon = ⊗-compatibleˡ M.associator.from ⟩∘⟨ refl⟩∘⟨ ⊗-compatibleʳ M.associator.from
             ○ refl⟩∘⟨ ⟺ F.homomorphism
             ○ [ IOO⇒Functor F ]-resp-∘ M.pentagon
             ○ F.homomorphism

  monoidal : Monoidal (pack′ D)
  monoidal = monoidalHelper (pack′ D) record
    { ⊗ = ⊗
    ; unit = M.unit
    ; unitorˡ = [ IOO⇒Functor F ]-resp-≅ M.unitorˡ
    ; unitorʳ = [ IOO⇒Functor F ]-resp-≅ M.unitorʳ
    ; associator = [ IOO⇒Functor F ]-resp-≅ M.associator
    ; unitorˡ-commute = unitorˡ-commute
    ; unitorʳ-commute = unitorʳ-commute
    ; assoc-commute = assoc-commute
    ; triangle = triangle
    ; pentagon = pentagon
    }
