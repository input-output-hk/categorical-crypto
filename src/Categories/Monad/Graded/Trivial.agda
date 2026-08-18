{-# OPTIONS --safe --without-K #-}

-- The trivial grading.  `One` has one object and one morphism, so grading by it
-- is no grading at all: every coercion is the identity and the graded laws
-- collapse to the ungraded ones.  This is how an ungraded monad, and a morphism
-- of two of them, enter the graded theory.

open import Data.Unit using (tt)
open import Level

open import Categories.Category
open import Categories.Category.Instance.One
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Instance.One
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal.Properties using (idF-Monoidal)
open import Categories.Monad.Construction.Kleisli using (KleisliTriple)
open import Categories.Monad.Graded
open import Categories.Monad.Graded.Morphism
open import Categories.Monad.Relative using () renaming (Monad to RMonad)

module Categories.Monad.Graded.Trivial where

private variable o ℓ e o′ ℓ′ e′ : Level

Oneᴹ : MonoidalCategory o ℓ e
Oneᴹ = record { U = One ; monoidal = One-Monoidal }

module _ {𝒞 : Category o′ ℓ′ e′} (K : KleisliTriple 𝒞) where

  private
    module 𝒞 = Category 𝒞
    module K = RMonad K
    open 𝒞.HomReasoning

  ungraded : GradedKleisliTriple (Oneᴹ {o} {ℓ} {e}) 𝒞
  ungraded = record
    { T₀               = λ _ → K.F₀
    ; ext              = λ _ → K.extend
    ; return           = K.unit
    ; sub              = λ _ → 𝒞.id
    ; ext-identityˡ    = 𝒞.identityˡ ○ K.identityˡ
    ; ext-identityʳ    = 𝒞.identityˡ ○ K.identityʳ
    ; ext-assoc        = K.assoc ○ ⟺ 𝒞.identityˡ
    ; ext-resp-≈       = K.extend-≈
    ; sub-commute      = 𝒞.identityʳ ○ K.extend-≈ 𝒞.identityˡ ○ ⟺ 𝒞.identityˡ
    ; sub-identity     = 𝒞.Equiv.refl
    ; sub-homomorphism = ⟺ 𝒞.identity²
    ; sub-resp-≈       = λ _ → 𝒞.Equiv.refl
    }

-- `κ-sub` is vacuous here, so what is left is exactly the two laws of an
-- ungraded monad morphism.
module _ {oᵢ ℓᵢ eᵢ : Level} {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′}
  (K : KleisliTriple 𝒞) (K′ : KleisliTriple 𝒟) (F : Functor 𝒞 𝒟)
  where

  private
    module 𝒟 = Category 𝒟
    module K = RMonad K
    module K′ = RMonad K′
    module F = Functor F
    open 𝒟.HomReasoning

  module _ (κ : Components (ungraded K {oᵢ} {ℓᵢ} {eᵢ}) (ungraded K′) F (idF-Monoidal Oneᴹ))
    where

    -- `ungraded`'s `T₀` ignores the grade, so `One`'s single object never shows
    -- up in a type unification could read it off: name it.
    private
      κ⋆ : ∀ {A} → 𝒟 [ F.₀ (K.F₀ A) , K′.F₀ (F.₀ A) ]
      κ⋆ = κ {lift tt}

    ungraded-morphism :
        (∀ {A} → 𝒟 [ κ⋆ 𝒟.∘ F.₁ (K.unit {A}) ≈ K′.unit ])
      → (∀ {A B} (f : 𝒞 [ A , K.F₀ B ])
          → 𝒟 [ κ⋆ 𝒟.∘ F.₁ (K.extend f) ≈ K′.extend (κ⋆ 𝒟.∘ F.₁ f) 𝒟.∘ κ⋆ ])
      → IsGradedKleisliMorphism (ungraded K {oᵢ} {ℓᵢ} {eᵢ}) (ungraded K′) F
                                (idF-Monoidal Oneᴹ) κ
    ungraded-morphism κ-unit κ-extend = record
      { κ-return = κ-unit ○ ⟺ 𝒟.identityˡ
      ; κ-ext    = λ f → κ-extend f ○ ⟺ 𝒟.identityˡ
      ; κ-sub    = λ _ → (refl⟩∘⟨ F.identity) ○ 𝒟.identityʳ ○ ⟺ 𝒟.identityˡ
      }
