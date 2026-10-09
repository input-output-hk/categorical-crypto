{-# OPTIONS --safe --without-K #-}

-- The quotient of a monoidal category by a congruence coarser than its hom
-- equality: same objects, morphisms and structure, with `_≈_` replaced, so
-- every law is the old one read through `≈⇒∼` and the projection is strong
-- monoidal on the nose.  A presheaf blind to the congruence descends with its
-- tests unchanged, which makes the comparison both `Mono` and `Epi`.

module Categories.Category.Monoidal.Construction.Quotient where

open import Data.Product
open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Core
open import Categories.Functor.Core
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties
open import Categories.Functor.Presheaf
open import Categories.Functor.Presheaf.Morphism
import Categories.Morphism as Mor
open import Categories.Morphism.Notation
open import Categories.NaturalTransformation.Core
open import Categories.NaturalTransformation.NaturalIsomorphism

-- The telescopes are spelled out, not generalized, so that a consumer can pass
-- the objects of a hom whose type does not determine them.
record MonoidalCongruence {o ℓ e} (𝕄 : MonoidalCategory o ℓ e) (e′ : Level)
       : Set (o ⊔ ℓ ⊔ e ⊔ suc e′) where
  open MonoidalCategory 𝕄
  field
    _∼_      : {A B : Obj} → Rel (A ⇒ B) e′
    ∼-equiv  : {A B : Obj} → IsEquivalence (_∼_ {A} {B})
    ≈⇒∼      : {A B : Obj} {f g : A ⇒ B} → f ≈ g → f ∼ g
    ∘-resp-∼ : {A B C : Obj} {f h : B ⇒ C} {g i : A ⇒ B} → f ∼ h → g ∼ i → (f ∘ g) ∼ (h ∘ i)
    ⊗-resp-∼ : {A B C D : Obj} {f h : A ⇒ B} {g i : C ⇒ D}
             → f ∼ h → g ∼ i → (f ⊗₁ g) ∼ (h ⊗₁ i)

  module ∼ {A B : Obj} = IsEquivalence (∼-equiv {A} {B})

module _ {o ℓ e e′} (𝕄 : MonoidalCategory o ℓ e) (Q : MonoidalCongruence 𝕄 e′) where
  private
    module M = MonoidalCategory 𝕄
    module I = IsStrongMonoidalFunctor (idF-IsStrongMonoidal 𝕄)
  open MonoidalCongruence Q

  private
    𝒬 : Category o ℓ e′
    𝒬 = record
      { Obj = M.Obj ; _⇒_ = M._⇒_ ; _≈_ = _∼_ ; id = M.id ; _∘_ = M._∘_
      ; assoc = ≈⇒∼ M.assoc ; sym-assoc = ≈⇒∼ M.sym-assoc ; identityˡ = ≈⇒∼ M.identityˡ
      ; identityʳ = ≈⇒∼ M.identityʳ ; identity² = ≈⇒∼ M.identity²
      ; equiv = ∼-equiv ; ∘-resp-≈ = ∘-resp-∼ }

    lift≅ : {A B : M.Obj} → M.U [ A ≅ B ] → 𝒬 [ A ≅ B ]
    lift≅ i = record
      { from = from ; to = to ; iso = record { isoˡ = ≈⇒∼ isoˡ ; isoʳ = ≈⇒∼ isoʳ } }
      where open Mor._≅_ i

  quotient : MonoidalCategory o ℓ e′
  quotient = record { U = 𝒬 ; monoidal = monoidalHelper 𝒬 record
    { ⊗ = record { F₀ = M.⊗.F₀ ; F₁ = M.⊗.F₁ ; identity = ≈⇒∼ M.⊗.identity
                 ; homomorphism = ≈⇒∼ M.⊗.homomorphism ; F-resp-≈ = uncurry ⊗-resp-∼ }
    ; unit = M.unit ; unitorˡ = lift≅ M.unitorˡ ; unitorʳ = lift≅ M.unitorʳ
    ; associator = lift≅ M.associator ; unitorˡ-commute = ≈⇒∼ M.unitorˡ-commute-from
    ; unitorʳ-commute = ≈⇒∼ M.unitorʳ-commute-from ; assoc-commute = ≈⇒∼ M.assoc-commute-from
    ; triangle = ≈⇒∼ M.triangle ; pentagon = ≈⇒∼ M.pentagon } }

  quotientF : StrongMonoidalFunctor 𝕄 quotient
  quotientF = record
    { F = record { F₀ = λ A → A ; F₁ = λ f → f ; identity = ∼.refl ; homomorphism = ∼.refl
                 ; F-resp-≈ = ≈⇒∼ }
    ; isStrongMonoidal = record
      { ε = lift≅ I.ε
      ; ⊗-homo = niHelper record
        { η = λ _ → M.id ; η⁻¹ = λ _ → M.id ; commute = λ f → ≈⇒∼ (I.⊗-homo.⇒.commute f)
        ; iso = λ X → record { isoˡ = ≈⇒∼ (I.⊗-homo.iso.isoˡ X)
                             ; isoʳ = ≈⇒∼ (I.⊗-homo.iso.isoʳ X) } }
      ; associativity = ≈⇒∼ I.associativity ; unitaryˡ = ≈⇒∼ I.unitaryˡ
      ; unitaryʳ = ≈⇒∼ I.unitaryʳ } }

  module _ {cs ℓs} (P : Presheaf M.U (Setoids cs ℓs))
           (resp : {A B : M.Obj} {f g : A M.⇒ B} → f ∼ g
                 → Setoids cs ℓs [ Functor.₁ P f ≈ Functor.₁ P g ]) where
    private module P = Functor P

    descend : Presheaf (MonoidalCategory.U quotient) (Setoids cs ℓs)
    descend = record { F₀ = P.₀ ; F₁ = P.₁ ; identity = P.identity
                     ; homomorphism = P.homomorphism ; F-resp-≈ = resp }

    descendᵛ : PresheafMorphism (StrongMonoidalFunctor.F quotientF) P descend
    descendᵛ = record { ν = ntHelper record
      { η = λ _ → record { to = λ x → x ; cong = λ e → e }
      ; commute = λ {_} {Y} _ → Setoid.refl (P.₀ Y) } }

    descendᵛ-mono : PresheafMorphism.Mono descendᵛ
    descendᵛ-mono e = e

    descendᵛ-epi : PresheafMorphism.Epi descendᵛ
    descendᵛ-epi {A} y = y , Setoid.refl (P.₀ A)
