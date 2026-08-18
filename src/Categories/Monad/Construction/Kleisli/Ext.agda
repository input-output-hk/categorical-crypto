{-# OPTIONS --safe --without-K #-}

-- Morphisms of Kleisli triples: `Monad⇒-id` pulled back along `Kleisli⇒Monad`.
-- `mkMorphism` and `Morphism`'s `θ-unit`/`θ-extend` translate between the
-- monad-level laws (naturality, unit, multiplication) and the triple-level ones
-- (unit, extend), so the two presentations carry the same data.

open import Level

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Monad.Construction.Kleisli
open import Categories.Monad.Morphism
open import Categories.Monad.Relative using (RMonad⇒Functor) renaming (Monad to RMonad)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (ntHelper)

module Categories.Monad.Construction.Kleisli.Ext {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning
open MR 𝒞

module _ (K : KleisliTriple 𝒞) where

  private
    module K = RMonad K
    module Kᶠ = Functor (RMonad⇒Functor K)

  -- The two ways a triple's monad extends along `f`; the graded sibling is
  -- `Categories.Monad.Graded.Ext.μT`.
  extend-μ : ∀ {A B} (f : A ⇒ K.F₀ B) → K.extend id ∘ Kᶠ.₁ f ≈ K.extend f
  extend-μ f = K.sym-assoc ○ K.extend-≈ (pullˡ K.identityʳ ○ identityˡ)

-- Upstream's `Monad⇒-id M N` carries `α : N.F ⇒ M.F`, so the *source* triple is
-- the second argument.
KleisliTriple⇒ : (K K′ : KleisliTriple 𝒞) → Set (o ⊔ ℓ ⊔ e)
KleisliTriple⇒ K K′ = Monad⇒-id (Kleisli⇒Monad 𝒞 K′) (Kleisli⇒Monad 𝒞 K)

-- `KleisliTriple⇒` is a defined type, so its two triples cannot be read back
-- off a morphism: both stay explicit here.
module _ (K K′ : KleisliTriple 𝒞) where

  private
    module K = RMonad K
    module K′ = RMonad K′
    module Kᶠ = Functor (RMonad⇒Functor K)
    module K′ᶠ = Functor (RMonad⇒Functor K′)

  module _ {θ : ∀ {A} → K.F₀ A ⇒ K′.F₀ A}
    (θ-unit : ∀ {A} → θ ∘ K.unit {A} ≈ K′.unit)
    (θ-extend : ∀ {A B} (f : A ⇒ K.F₀ B) → θ ∘ K.extend f ≈ K′.extend (θ ∘ f) ∘ θ)
    where

    private
      θ-natural : ∀ {A B} (f : A ⇒ B) → θ ∘ Kᶠ.₁ f ≈ K′ᶠ.₁ f ∘ θ
      θ-natural f = θ-extend _ ○ K′.extend-≈ (pullˡ θ-unit) ⟩∘⟨refl

    mkMorphism : KleisliTriple⇒ K K′
    mkMorphism = record
      { α         = ntHelper record { η = λ _ → θ ; commute = θ-natural }
      ; unit-comp = θ-unit
      ; mult-comp = λ {A} → begin
          θ ∘ K.extend id                        ≈⟨ θ-extend id ⟩
          K′.extend (θ ∘ id) ∘ θ                 ≈⟨ K′.extend-≈ identityʳ ⟩∘⟨refl ⟩
          K′.extend θ ∘ θ                        ≈˘⟨ extend-μ K′ θ ⟩∘⟨refl ⟩
          (K′.extend id ∘ K′ᶠ.₁ θ) ∘ θ           ≈⟨ assoc ⟩
          K′.extend id ∘ (K′ᶠ.₁ θ ∘ θ)           ≈˘⟨ refl⟩∘⟨ θ-natural θ ⟩
          K′.extend id ∘ (θ ∘ Kᶠ.₁ θ)            ∎
      }

  module Morphism (Θ : KleisliTriple⇒ K K′) where

    open Monad⇒-id Θ using (unit-comp; mult-comp) renaming (module α to α)

    θ : ∀ {A} → K.F₀ A ⇒ K′.F₀ A
    θ = α.η _

    θ-unit : ∀ {A} → θ ∘ K.unit {A} ≈ K′.unit
    θ-unit = unit-comp

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
