{-# OPTIONS --safe --without-K #-}

module Categories.Properties where

open import Categories.Category using (Category)
open import Categories.Category.Product using (Product; _⁂_; _※_; _※ⁿⁱ_)
open import Categories.Functor as F using (Functor; _∘F_)
open import Categories.Functor.Construction.Constant using (const; constʳ)
open import Categories.Morphism using (IsIso)
open import Categories.Morphism.Properties using (id-is-iso)
open import Categories.NaturalTransformation.NaturalIsomorphism as NI using (NaturalIsomorphism; niHelper; Functor-NI-setoid)

import Relation.Binary.Reasoning.Setoid as SetoidR

module _ {a b c} where
  ⁂-※ : {C D D' E E' : Category a b c}
      → (F : Functor C D) → (F' : Functor C D') → (G : Functor D E) → (G' : Functor D' E')
      → NaturalIsomorphism ((G ⁂ G') ∘F (F ※ F')) ((G ∘F F) ※ (G' ∘F F'))
  ⁂-※ {E = E} {E'} F F' G G' = niHelper record
    { η = λ _ → P.id
    ; η⁻¹ = λ _ → P.id
    ; commute = λ _ → let open P.HomReasoning in P.identityˡ ○ ⟺ P.identityʳ
    ; iso = λ _ → IsIso.iso (id-is-iso (Product E E'))
    }
    where module P = Category (Product E E')

  ∘F-const : ∀ {C D E : Category a b c} d
           → (F : Functor D E) → NaturalIsomorphism {C = C} (F ∘F const d) (const (Functor.F₀ F d))
  ∘F-const {E = E} d F = niHelper record
    { η = λ _ → E.id
    ; η⁻¹ = λ _ → E.id
    ; commute = λ _ → begin E.id E.∘ Functor.F₁ F _ ≈⟨ refl⟩∘⟨ Functor.identity F ⟩ E.id E.∘ E.id ∎
    ; iso = λ _ → IsIso.iso (id-is-iso E) }
    where module E = Category E
          open E.HomReasoning

  -×_ : {C D : Category a b c} → D .Category.Obj → Functor C (Product C D)
  -×_ {C} {D} d = constʳ {C = D} {D = C} d

  ⁂-× : {C D E : Category a b c} → (G : Functor D E) → (d : D .Category.Obj)
      → NaturalIsomorphism ((F.id {C = C} ⁂ G) ∘F -× d) (-× Functor.F₀ G d)
  ⁂-× G d = begin
    (F.id ⁂ G) ∘F -× d ≈⟨ ⁂-※ _ _ F.id G ⟩
    ((F.id ∘F F.id) ※ (G ∘F const d)) ≈⟨ NI.unitorˡ ※ⁿⁱ ∘F-const d G ⟩
    -× Functor.F₀ G d ∎
    where open SetoidR (Functor-NI-setoid _ _)
