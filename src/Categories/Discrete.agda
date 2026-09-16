{-# OPTIONS --safe --without-K #-}

module Categories.Discrete where

open import Level using (0ℓ)

open import Categories.Category using (Category; _[_,_]; _[_≈_]; _[_∘_])
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Functor using (Functor)

open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

module Discrete (X : Set) where

  Discrete : Category 0ℓ 0ℓ 0ℓ
  Discrete = categoryHelper record
    { Obj       = X
    ; _⇒_       = _≡_
    ; _≈_       = λ _ _ → ⊤ -- if we used _≡_ here then it's only discrete if we assume K
    ; id        = refl
    ; _∘_       = λ p q → trans q p
    ; assoc     = _
    ; identityˡ = _
    ; identityʳ = _
    ; equiv     = record { refl = _ ; sym = _ ; trans = _ }
    ; ∘-resp-≈  = _
    }

  Discrete-NaturalD : {D : Category 0ℓ 0ℓ 0ℓ} {F G : Functor Discrete D}
                      (η : ∀ X → D [ Functor.F₀ F X , Functor.F₀ G X ])
                    → ∀ {X Y} (f : Discrete [ X , Y ])
                        → D [ D [ η Y ∘ Functor.F₁ F f ] ≈ D [ Functor.F₁ G f ∘ η X ] ]
  Discrete-NaturalD {D} {F} {G} η refl = begin
    η _ D.∘ Functor.F₁ F _
      ≈⟨ refl⟩∘⟨ Functor.identity F ⟩
    η _ D.∘ D.id
      ≈⟨ D.identityʳ ○ ⟺ D.identityˡ ⟩
    D.id D.∘ η _
      ≈⟨ Functor.identity G ⟩∘⟨refl ⟨
    Functor.F₁ G _ D.∘ η _ ∎
    where module D = Category D
          open D.HomReasoning
