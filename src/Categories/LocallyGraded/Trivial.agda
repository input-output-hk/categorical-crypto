{-# OPTIONS --safe --without-K #-}

-- The trivial grading of an ordinary category

module Categories.LocallyGraded.Trivial where

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded

Trivial : ∀ {o ℓ e o′ ℓ′ e′} (ℐ : MonoidalCategory o ℓ e) → Category o′ ℓ′ e′
        → LocallyGradedCategory ℐ o′ ℓ′ e′
Trivial ℐ C = record
  { Obj              = Obj
  ; Hom              = λ _ → _⇒_
  ; _≈_              = _≈_
  ; equiv            = equiv
  ; sub[_]           = λ _ f → f
  ; sub-identity     = Equiv.refl
  ; sub-homomorphism = Equiv.refl
  ; sub-resp-≈       = λ _ f≈g → f≈g
  ; id               = id
  ; _∙_              = _∘_
  ; ∙-resp-≈         = ∘-resp-≈
  ; identityˡ        = identityˡ
  ; identityʳ        = identityʳ
  ; assoc            = assoc
  ; interchange      = Equiv.refl
  }
  where open Category C
