{-# OPTIONS --safe --without-K #-}

open import Categories.Category.Core
open import Categories.Category.Monoidal.Construction.Transport
open import Categories.Category.Monoidal.Core
open import Categories.Category.Monoidal.Symmetric
open import Categories.Category.Unbundled.Properties
open import Categories.Functor.Bifunctor
open import Categories.Functor.IdentityOnObjects
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism
import Categories.Category.Unbundled as Unbundled

open import Data.Product

module Categories.Category.Monoidal.Construction.Transport.Symmetric
  {o ℓ e ℓ′ e′} {Obj : Set o}
  {C : Unbundled.Category Obj ℓ e} {D : Unbundled.Category Obj ℓ′ e′}
  {M : Monoidal (pack′ C)} {F : IdentityOnObjects C D}
  (T : Transport C D M F) (S : Symmetric {C = pack′ C} M) where

private
  module C = Category (pack′ C)
  module D = Category (pack′ D)
  module M = Monoidal M
  module F = IdentityOnObjects F
  module S = Symmetric S

open D using (_⇒_; _≈_; _∘_; id)
open D.HomReasoning
open Transport T

private
  variable A B X : Obj

  σ⇒ : A M.⊗₀ B C.⇒ B M.⊗₀ A
  σ⇒ {A} {B} = S.braiding.⇒.η (A , B)

opaque
  commutative : F.F₁ (σ⇒ {A} {B}) ∘ F.F₁ (σ⇒ {B} {A}) ≈ id
  commutative = [ IOO⇒Functor F ]-resp-inverse S.commutative

  hexagon₁ : id ⊗₁ F.F₁ (σ⇒ {A} {X}) ∘ F.F₁ M.associator.from ∘ F.F₁ (σ⇒ {A} {B}) ⊗₁ id
             ≈ F.F₁ M.associator.from ∘ F.F₁ σ⇒ ∘ F.F₁ M.associator.from
  hexagon₁ = ⊗-compatibleˡ σ⇒ ⟩∘⟨ refl⟩∘⟨ ⊗-compatibleʳ σ⇒
           ○ refl⟩∘⟨ ⟺ F.homomorphism
           ○ [ IOO⇒Functor F ]-resp-∘ S.hexagon₁
           ○ F.homomorphism
           ○ refl⟩∘⟨ F.homomorphism

module _ (braiding-commute : ∀ {A B X Y} {f : A ⇒ B} {g : X ⇒ Y} →
                             F.F₁ σ⇒ ∘ f ⊗₁ g ≈ g ⊗₁ f ∘ F.F₁ σ⇒) where

  braiding : NaturalIsomorphism ⊗ (flip-bifunctor ⊗)
  braiding = niHelper record
    { η   = λ (A , B) → F.F₁ (σ⇒ {A} {B})
    ; η⁻¹ = λ (A , B) → F.F₁ (σ⇒ {B} {A})
    ; commute = λ _ → braiding-commute
    ; iso = λ _ → record
        { isoˡ = commutative
        ; isoʳ = commutative
        }
    }

  opaque
    hexagon₂ : ∀ {A B X} →
                 (F.F₁ (σ⇒ {A} {X}) ⊗₁ id ∘ F.F₁ M.associator.to) ∘ id ⊗₁ F.F₁ (σ⇒ {B} {X})
                 ≈ (F.F₁ M.associator.to ∘ F.F₁ σ⇒) ∘ F.F₁ M.associator.to
    hexagon₂ = Symmetric.hexagon₂ (symmetricHelper {C = pack′ D} monoidal record
      { braiding    = braiding
      ; commutative = commutative
      ; hexagon     = hexagon₁
      })

  symmetric : Symmetric {C = pack′ D} monoidal
  symmetric = record
    { braided = record { braiding = braiding ; hexagon₁ = hexagon₁ ; hexagon₂ = hexagon₂ }
    ; commutative = commutative
    }
