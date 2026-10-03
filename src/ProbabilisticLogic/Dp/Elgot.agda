{-# OPTIONS --safe --without-K --guardedness #-}

-- Uniformity of `iterₚ` along an arbitrary pure state map `θ : S → S′` (no
-- invertibility), applied to the exit state as well — the loop points and the
-- exits share one state type; `Iter.Transfer.iterₚ-transfer` takes the two maps
-- separately.  The context law is its `θ = (c ,_)` instance.  `φ k m`
-- case-splits on the `⊎`-summand while a padded state map does not, so the two
-- agree only pointwise; `Dp.Reasoning.map-eq` bridges that.

open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational
open import Data.Sum.Base hiding (map₁)
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Iter.Transfer
open import ProbabilisticLogic.Dp.Reasoning

module ProbabilisticLogic.Dp.Elgot where

-- Objects are bound explicitly, not as `variable`s: see `Dp.Iter`.
private variable ℓ : Level

------------------------------------------------------------------------
-- Uniformity along an arbitrary PURE state map

φ-map₁ : {S S′ A B : Set ℓ} (θ : S → S′) (r : S × (B ⊎ A))
       → φ (map₁ {C = A} θ) (map₁ {C = B} θ) r ≡ map₁ θ r
φ-map₁ θ (s , inj₁ b) = refl
φ-map₁ θ (s , inj₂ p) = refl

iterₚ-uniform : {S S′ A B : Set ℓ} (u : Body S A B) (v : Body S′ A B) (θ : S → S′)
              → (∀ sa → v (map₁ θ sa) ≈ₚ mapₚ (map₁ θ) (u sa))
              → (sa : S × A) → iterₚ v (map₁ θ sa) ≈ₚ mapₚ (map₁ θ) (iterₚ u sa)
iterₚ-uniform u v θ h sa =
  iterₚ-transfer u v (map₁ θ) (map₁ θ) sim sa
  where
  sim : ∀ sa′ → v (map₁ θ sa′) ≈ₚ mapₚ (φ (map₁ θ) (map₁ θ)) (u sa′)
  sim sa′ = ≈ₚ-trans _ _ _ (h sa′)
              (map-eq (u sa′) (map₁ θ) (φ (map₁ θ) (map₁ θ)) (λ r → sym (φ-map₁ θ r)))
