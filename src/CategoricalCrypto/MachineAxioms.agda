{-# OPTIONS --safe --without-K #-}

-- An axiomatized machine layer

module CategoricalCrypto.MachineAxioms where

open import Data.Nat as ℕ using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties
open import Data.Sum
open import Function using (case_of_)
open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality

open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

record MachineAxioms (o ℓ e os ℓs qs : Level) : Set (suc (o ⊔ ℓ ⊔ e ⊔ os ⊔ ℓs ⊔ qs)) where
  field 𝕄 : MonoidalCategory o ℓ e

  module 𝕄 = MonoidalCategory 𝕄
  open 𝕄
  open MonoidalUtilities.Shorthands monoidal

  field
    Ω   : Obj            -- the verdict channel
    Obs : Setoid os ℓs   -- closed-run observations

  module Obs = Setoid Obs

  field
    ⟦_⟧ : unit ⇒ Ω → Obs.Carrier
    adv : Obs.Carrier → Obs.Carrier → ℚ -- distinguishing advantage
    QB  : ℕ → ∀ {A B} → A ⇒ B → Set qs  -- query bound: `QB c h`
    -- reads "h is c-query-bounded": one codomain-side activation
    -- causes at most c completed domain-side events

    ⟦⟧-resp-≈ : ∀ {f g : unit ⇒ Ω} → f ≈ g → ⟦ f ⟧ Obs.≈ ⟦ g ⟧

    adv-sym      : ∀ x y → adv x y ≡ adv y x
    adv-triangle : ∀ x y z → adv x z ℚ.≤ adv x y ℚ.+ adv y z
    adv-≈⇒0      : ∀ {x y} → x Obs.≈ y → adv x y ≡ 0ℚ

    qb-id     : ∀ {A} → QB 1 (id {A})
    qb-∘      : ∀ {A B C c c′} {g : B ⇒ C} {f : A ⇒ B} → QB c g → QB c′ f → QB (c ℕ.* c′) (g ∘ f)
    qb-⊗      : ∀ {A B C D c c′} {f : A ⇒ B} {h : C ⇒ D} → QB c f → QB c′ h → QB (c ℕ.⊔ c′) (f ⊗₁ h)
    qb-resp-≈ : ∀ {A B c} {f g : A ⇒ B} → f ≈ g → QB c f → QB c g
    qb-mono   : ∀ {A B c c′} {f : A ⇒ B} → c ℕ.≤ c′ → QB c f → QB c′ f
    qb-α⇒     : ∀ {A B C} → QB 1 (α⇒ {A} {B} {C})
    qb-α⇐     : ∀ {A B C} → QB 1 (α⇐ {A} {B} {C})
    qb-λ⇒     : ∀ {A} → QB 1 (λ⇒ {A})
    qb-λ⇐     : ∀ {A} → QB 1 (λ⇐ {A})
    qb-ρ⇒     : ∀ {A} → QB 1 (ρ⇒ {A})
    qb-ρ⇐     : ∀ {A} → QB 1 (ρ⇐ {A})

  -- The one further hypothesis the ℰᵗᵛ layer needs (`VanishingTV`): transport
  -- along an object LOOP is observationally invisible on closures. Implied by
  -- `UIP Obj`, and plausible precisely because `≈` is observational. Not a
  -- field: only `VanishingTV` proves anything with it, the ℰᵗᵛ modules above it
  -- merely thread it.
  HomTransportTrivial : Set (o ⊔ ℓ ⊔ e)
  HomTransportTrivial = ∀ {X} (p : X ≡ X) (m : unit ⇒ X) → subst (unit ⇒_) p m ≈ m

  adv-refl : ∀ {x} → adv x x ≡ 0ℚ
  adv-refl = adv-≈⇒0 Obs.refl

  adv-nonneg : ∀ x y → 0ℚ ℚ.≤ adv x y
  adv-nonneg x y = case ≤-total 0ℚ (adv x y) of λ where
      (inj₁ 0≤q) → 0≤q
      (inj₂ q≤0) → ≤-trans 0≤q+q (≤-trans (+-monoʳ-≤ (adv x y) q≤0)
                                          (≤-reflexive (+-identityʳ (adv x y))))
    where
    0≤q+q : 0ℚ ℚ.≤ adv x y ℚ.+ adv x y
    0≤q+q = subst₂ ℚ._≤_ adv-refl (cong (adv x y ℚ.+_) (adv-sym y x)) (adv-triangle x y x)
