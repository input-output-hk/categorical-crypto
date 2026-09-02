{-# OPTIONS --safe --without-K #-}

-- Morphisms of Kleisli triples in two presentations, proved equivalent:
-- `KleisliTriple⇒`, a component family with the unit and extend laws, and
-- `KleisliTriple⇒ᴹ`, `Monad⇒-id` pulled back along `Kleisli⇒Monad`.  `⇒↔⇒ᴹ` is the
-- translation, an `Inverse` of the setoids that compare morphisms by their component
-- family alone: the law fields are not propositions, so a round-trip identity of the
-- *records* is not statable, and comparing components is what makes the two agree.

open import Level

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Monad.Construction.Kleisli
open import Categories.Monad.Morphism
open import Categories.Monad.Relative using (RMonad⇒Functor) renaming (Monad to RMonad)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

open import Data.Product using (_,_)
open import Function.Bundles using (Inverse)
open import Relation.Binary.Bundles using (Setoid)

module Categories.Monad.Construction.Kleisli.Ext {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning
open MR 𝒞

module _ (K : KleisliTriple 𝒞) where

  private
    module K = RMonad K
    module Kᶠ = Functor (RMonad⇒Functor K)

  extend-μ : ∀ {A B} (f : A ⇒ K.F₀ B) → K.extend id ∘ Kᶠ.₁ f ≈ K.extend f
  extend-μ f = K.sym-assoc ○ K.extend-≈ (pullˡ K.identityʳ ○ identityˡ)

record KleisliTriple⇒ (K K′ : KleisliTriple 𝒞) : Set (o ⊔ ℓ ⊔ e) where
  private
    module K = RMonad K
    module K′ = RMonad K′
  field
    θ        : ∀ {A} → K.F₀ A ⇒ K′.F₀ A
    θ-unit   : ∀ {A} → θ ∘ K.unit {A} ≈ K′.unit
    θ-extend : ∀ {A B} (f : A ⇒ K.F₀ B) → θ ∘ K.extend f ≈ K′.extend (θ ∘ f) ∘ θ

-- Upstream's `Monad⇒-id M N` carries `α : N.F ⇒ M.F`, so the *source* triple is
-- the second argument.
KleisliTriple⇒ᴹ : (K K′ : KleisliTriple 𝒞) → Set (o ⊔ ℓ ⊔ e)
KleisliTriple⇒ᴹ K K′ = Monad⇒-id (Kleisli⇒Monad 𝒞 K′) (Kleisli⇒Monad 𝒞 K)

-- `KleisliTriple⇒ᴹ` is a defined type, so its two triples cannot be read back
-- off a morphism: both stay explicit here.
module _ (K K′ : KleisliTriple 𝒞) where

  private
    module K = RMonad K
    module K′ = RMonad K′
    module Kᶠ = Functor (RMonad⇒Functor K)
    module K′ᶠ = Functor (RMonad⇒Functor K′)

  toMonad⇒ : KleisliTriple⇒ K K′ → KleisliTriple⇒ᴹ K K′
  toMonad⇒ Θ = record
    { α         = ntHelper record { η = λ _ → θ ; commute = θ-natural }
    ; unit-comp = θ-unit
    ; mult-comp = begin
        θ ∘ K.extend id                        ≈⟨ θ-extend id ⟩
        K′.extend (θ ∘ id) ∘ θ                 ≈⟨ K′.extend-≈ identityʳ ⟩∘⟨refl ⟩
        K′.extend θ ∘ θ                        ≈˘⟨ extend-μ K′ θ ⟩∘⟨refl ⟩
        (K′.extend id ∘ K′ᶠ.₁ θ) ∘ θ           ≈⟨ assoc ⟩
        K′.extend id ∘ (K′ᶠ.₁ θ ∘ θ)           ≈˘⟨ refl⟩∘⟨ θ-natural θ ⟩
        K′.extend id ∘ (θ ∘ Kᶠ.₁ θ)            ∎
    }
    where
      open KleisliTriple⇒ Θ

      θ-natural : ∀ {A B} (f : A ⇒ B) → θ ∘ Kᶠ.₁ f ≈ K′ᶠ.₁ f ∘ θ
      θ-natural f = θ-extend _ ○ K′.extend-≈ (pullˡ θ-unit) ⟩∘⟨refl

  fromMonad⇒ : KleisliTriple⇒ᴹ K K′ → KleisliTriple⇒ K K′
  fromMonad⇒ Θ = record { θ = θ ; θ-unit = unit-comp ; θ-extend = θ-extend }
    where
      open Monad⇒-id Θ using (unit-comp; mult-comp) renaming (module α to α)

      θ : ∀ {A} → K.F₀ A ⇒ K′.F₀ A
      θ = α.η _

      θ-extend : ∀ {A B} (f : A ⇒ K.F₀ B) → θ ∘ K.extend f ≈ K′.extend (θ ∘ f) ∘ θ
      θ-extend f = begin
        θ ∘ K.extend f                             ≈˘⟨ refl⟩∘⟨ extend-μ K f ⟩
        θ ∘ (K.extend id ∘ Kᶠ.₁ f)                 ≈⟨ sym-assoc ⟩
        (θ ∘ K.extend id) ∘ Kᶠ.₁ f                 ≈⟨ mult-comp ⟩∘⟨refl ⟩
        (K′.extend id ∘ (θ ∘ Kᶠ.₁ θ)) ∘ Kᶠ.₁ f     ≈⟨ assoc ○ refl⟩∘⟨ assoc ⟩
        K′.extend id ∘ (θ ∘ (Kᶠ.₁ θ ∘ Kᶠ.₁ f))     ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ Kᶠ.homomorphism ⟩
        K′.extend id ∘ (θ ∘ Kᶠ.₁ (θ ∘ f))          ≈⟨ refl⟩∘⟨ α.commute (θ ∘ f) ⟩
        K′.extend id ∘ (K′ᶠ.₁ (θ ∘ f) ∘ θ)         ≈⟨ sym-assoc ⟩
        (K′.extend id ∘ K′ᶠ.₁ (θ ∘ f)) ∘ θ         ≈⟨ extend-μ K′ (θ ∘ f) ⟩∘⟨refl ⟩
        K′.extend (θ ∘ f) ∘ θ                      ∎

  ⇒-setoid : Setoid (o ⊔ ℓ ⊔ e) (o ⊔ e)
  ⇒-setoid = record
    { Carrier       = KleisliTriple⇒ K K′
    ; _≈_           = λ Θ Θ′ → ∀ {A} → KleisliTriple⇒.θ Θ {A} ≈ KleisliTriple⇒.θ Θ′
    ; isEquivalence = record
        { refl = Equiv.refl ; sym = λ p → Equiv.sym p ; trans = λ p q → Equiv.trans p q }
    }

  ⇒ᴹ-setoid : Setoid (o ⊔ ℓ ⊔ e) (o ⊔ e)
  ⇒ᴹ-setoid = record
    { Carrier       = KleisliTriple⇒ᴹ K K′
    ; _≈_           = λ Θ Θ′ → ∀ {A} → NaturalTransformation.η (Monad⇒-id.α Θ) A
                                     ≈ NaturalTransformation.η (Monad⇒-id.α Θ′) A
    ; isEquivalence = record
        { refl = Equiv.refl ; sym = λ p → Equiv.sym p ; trans = λ p q → Equiv.trans p q }
    }

  -- Both translations are the identity on components, so every law is `λ p → p`.
  ⇒↔⇒ᴹ : Inverse ⇒-setoid ⇒ᴹ-setoid
  ⇒↔⇒ᴹ = record
    { to        = toMonad⇒
    ; from      = fromMonad⇒
    ; to-cong   = λ p → p
    ; from-cong = λ p → p
    ; inverse   = (λ p → p) , (λ p → p)
    }
