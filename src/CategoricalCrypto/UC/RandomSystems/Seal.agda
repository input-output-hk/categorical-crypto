{-# OPTIONS --safe --without-K --guardedness #-}

-- Behavioural equality as a congruence of the sealed `𝔾ᵒ`, built where the seal
-- is transparent, with its coercions exported from inside the block, one per
-- shape — `UC.Model.Seal`'s disciplines.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient

open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Level

open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Machine.Behaviour.Congruence
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal

module CategoricalCrypto.UC.RandomSystems.Seal where

private
  module Ap = AllPositive ℚ-refinement Approximationᴹ
  module G = MonoidalCategory 𝔾ᵒ

opaque
  unfolding 𝔾ᵒ ifaceᵒ procᵒ unprocᵒ

  congᴿ : MonoidalCongruence 𝔾ᵒ 0ℓ
  congᴿ = record
    { _∼_      = λ {X} {Y} → _≈ᴿ_ {proj₁ X ⊎ proj₂ Y} {proj₂ X ⊎ proj₁ Y}
    ; ∼-equiv  = ≈ᴿ-isEquivalence
    ; ≈⇒∼      = ≈ᴹ⇒≈ᴿ
    ; ∘-resp-∼ = λ {A} {B} {C} {f} {h} {g} {i} →
        composeᴳ-resp-≈ᴿ {proj₁ A} {proj₂ A} {proj₁ B} {proj₂ B} {proj₁ C} {proj₂ C} {f} {h} {g} {i}
    ; ⊗-resp-∼ = λ {A} {B} {C} {D} {f} {h} {g} {i} →
        ⊗₁ᴳ-resp-≈ᴿ {proj₁ A} {proj₂ A} {proj₁ B} {proj₂ B} {proj₁ C} {proj₂ C} {proj₁ D} {proj₂ D}
                   {f} {h} {g} {i}
    }

  ∼ᴿ⇒Obs : {u v : 𝟘ᵒ G.⇒ Ωᵒ} → MonoidalCongruence._∼_ congᴿ u v → Obs u Ap.∼ᵃ Obs v
  ∼ᴿ⇒Obs {u} {v} e ε pos =
    ≈ₚ[]-resp (≈sym (runᴹ≈runˢ u (ask tt out))) (≈sym (runᴹ≈runˢ v (ask tt out)))
              (e (closeˢ (ask tt out)) ε pos)

  ≈ᴿ⇒∼ᴿ : {A B : Iface} {f g : Proc A B} → f ≈ᴿ g → MonoidalCongruence._∼_ congᴿ (procᵒ f) (procᵒ g)
  ≈ᴿ⇒∼ᴿ e = e

  ∼ᴿ⇒≈ᴿ : {A B : Iface} {f g : ifaceᵒ A G.⇒ ifaceᵒ B}
        → MonoidalCongruence._∼_ congᴿ f g → unprocᵒ f ≈ᴿ unprocᵒ g
  ∼ᴿ⇒≈ᴿ e = e
