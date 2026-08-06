{-# OPTIONS --safe --without-K #-}

-- The naive graded Kleisli construction: a graded Kleisli triple ℳ presents a
-- locally ℐ-graded category whose grade-X homs are the bare Kleisli maps
-- A ⇒ T₀ X B (McDermott–Uustalu, "Flexibly graded monads and graded
-- algebras", MPC 2022).

module Categories.LocallyGraded.Kleisli where

open import Level

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.LocallyGraded
open import Categories.Monad.Graded
import Categories.Morphism.Reasoning as MR

module _ {o ℓ e o′ ℓ′ e′ : Level} {ℐ : MonoidalCategory o ℓ e} {𝒞 : Category o′ ℓ′ e′} where
  private module C where
    open Category 𝒞 public
    open HomReasoning public
    open MR 𝒞 public

  naiveKleisli : GradedKleisliTriple ℐ 𝒞 → LocallyGradedCategory ℐ o′ ℓ′ e′
  naiveKleisli ℳ = record
    { Obj              = C.Obj
    ; Hom              = λ X A B → A C.⇒ T₀ X B
    ; _≈_              = C._≈_
    ; equiv            = C.equiv
    ; sub[_]           = λ a f → sub a C.∘ f
    ; sub-identity     = C.elimˡ sub-identity
    ; sub-homomorphism = C.pushˡ sub-homomorphism
    ; sub-resp-≈       = λ ea ef → C.∘-resp-≈ (sub-resp-≈ ea) ef
    ; id               = return
    ; _∙_              = λ {X} h f → ext X h C.∘ f
    ; ∙-resp-≈         = λ eh ef → C.∘-resp-≈ (ext-resp-≈ eh) ef
    ; identityˡ        = let open C in pullˡ ext-identityˡ ○ identityˡ
    ; identityʳ        = ext-identityʳ
    ; assoc            = let open C in (ext-assoc ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ assoc)
    ; interchange      = let open C in pullˡ sub-commute ○ assoc
    }
    where open GradedKleisliTriple ℳ
