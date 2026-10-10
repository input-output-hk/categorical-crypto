{-# OPTIONS --safe --without-K #-}

-- Kleisli triples as graded ones over the terminal monoidal category `One`, and
-- the unit of any ℐ as a grade functor `Oneᴹ → ℐ`.

open import Data.Product.Base
open import Data.Unit
open import Level

open import Categories.Category
open import Categories.Category.Instance.One
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Instance.One
import Categories.Category.Monoidal.Properties as MonoidalProperties
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties
open import Categories.Monad.Construction.Kleisli
open import Categories.Monad.Construction.Kleisli.Ext
open import Categories.Monad.Graded
open import Categories.Monad.Graded.Morphism
open import Categories.Monad.Relative using () renaming (Monad to RMonad)
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism

module Categories.Monad.Graded.Trivial where

private variable o ℓ e o′ ℓ′ e′ : Level

Oneᴹ : MonoidalCategory o ℓ e
Oneᴹ = record { U = One ; monoidal = One-Monoidal }

-- A setup restricted along it (`CategoricalCrypto.Abstract2.Regrade`) keeps one
-- ancilla and one simulator, both the unit.
unitᴹ : (ℐ : MonoidalCategory o ℓ e) → StrongMonoidalFunctor (Oneᴹ {o′} {ℓ′} {e′}) ℐ
unitᴹ ℐ = record
  { F = record
    { F₀ = λ _ → unit ; F₁ = λ _ → id ; identity = Equiv.refl ; homomorphism = ⟺ identity²
    ; F-resp-≈ = λ _ → Equiv.refl }
  ; isStrongMonoidal = record
    { ε = Mor.≅.refl U
    ; ⊗-homo = niHelper record
      { η = λ _ → unitorˡ.from ; η⁻¹ = λ _ → unitorˡ.to
      ; commute = λ _ → elimʳ ⊗.identity ○ ⟺ identityˡ ; iso = λ _ → unitorˡ.iso }
    ; associativity = identityˡ ○ refl⟩∘⟨ ⊗.F-resp-≈ (coherence₃ , Equiv.refl) ○ ⟺ (refl⟩∘⟨ triangle)
    ; unitaryˡ = identityˡ ○ elimʳ ⊗.identity
    ; unitaryʳ = identityˡ ○ elimʳ ⊗.identity ○ coherence₃ } }
  where
    open MonoidalCategory ℐ
    open HomReasoning
    open MR U
    open MonoidalProperties monoidal

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

-- `κ-sub` is vacuous here, so what is left is exactly the two laws of a
-- morphism of triples along `F`.
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

    private
      κ⋆ : ∀ {A} → 𝒟 [ F.₀ (K.F₀ A) , K′.F₀ (F.₀ A) ]
      κ⋆ = κ {lift tt}

    ungraded-filler :
        (∀ {A} → 𝒟 [ κ⋆ 𝒟.∘ F.₁ (K.unit {A}) ≈ K′.unit ])
      → (∀ {A B} (f : 𝒞 [ A , K.F₀ B ])
          → 𝒟 [ κ⋆ 𝒟.∘ F.₁ (K.extend f) ≈ K′.extend (κ⋆ 𝒟.∘ F.₁ f) 𝒟.∘ κ⋆ ])
      → IsGradedKleisliMorphism (ungraded K {oᵢ} {ℓᵢ} {eᵢ}) (ungraded K′) F
                                (idF-Monoidal Oneᴹ) κ
    ungraded-filler κ-unit κ-extend = record
      { κ-return = κ-unit ○ ⟺ 𝒟.identityˡ
      ; κ-ext    = λ f → κ-extend f ○ ⟺ 𝒟.identityˡ
      ; κ-sub    = λ _ → (refl⟩∘⟨ F.identity) ○ 𝒟.identityʳ ○ ⟺ 𝒟.identityˡ
      }

module _ {oᵢ ℓᵢ eᵢ : Level} {𝒞 : Category o ℓ e}
  (K K′ : KleisliTriple 𝒞) (Θ : KleisliTriple⇒ 𝒞 K K′) where

  open KleisliTriple⇒ Θ

  ungraded-morphism :
    IsGradedKleisliMorphism (ungraded K {oᵢ} {ℓᵢ} {eᵢ}) (ungraded K′) idF
                            (idF-Monoidal Oneᴹ) θ
  ungraded-morphism = ungraded-filler K K′ idF θ θ-unit θ-extend
