{-# OPTIONS --safe --without-K --guardedness #-}

-- Uniformity of `iterₚ` along an arbitrary pure state map `θ : S → S′` (no
-- invertibility); the context law is its `θ = (c ,_)` instance.  `φ k m`
-- case-splits on the `⊎`-summand while a padded state map does not, so the two
-- agree only pointwise; `Dp.Reasoning.map-eq` bridges that.

open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational
open import Data.Sum.Base
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

padₛ : {S S′ X : Set ℓ} → (S → S′) → S × X → S′ × X
padₛ θ (s , x) = θ s , x

φ-padₛ : {S S′ A B : Set ℓ} (θ : S → S′) (r : S × (B ⊎ A))
       → φ (padₛ {X = A} θ) (padₛ {X = B} θ) r ≡ padₛ θ r
φ-padₛ θ (s , inj₁ b) = refl
φ-padₛ θ (s , inj₂ p) = refl

iterₚ-uniform : {S S′ A B : Set ℓ} (u : Body S A B) (v : Body S′ A B) (θ : S → S′)
              → (∀ sa → v (padₛ θ sa) ≈ₚ mapₚ (padₛ θ) (u sa))
              → (sa : S × A) → iterₚ v (padₛ θ sa) ≈ₚ mapₚ (padₛ θ) (iterₚ u sa)
iterₚ-uniform u v θ h sa =
  iterₚ-transfer u v (padₛ θ) (padₛ θ) sim sa
  where
  sim : ∀ sa′ → v (padₛ θ sa′) ≈ₚ mapₚ (φ (padₛ θ) (padₛ θ)) (u sa′)
  sim sa′ = ≈ₚ-trans _ _ _ (h sa′)
              (map-eq (u sa′) (padₛ θ) (φ (padₛ θ) (padₛ θ)) (λ r → sym (φ-padₛ θ r)))

iterₚ-ctx : {C S A B : Set ℓ} (u : Body S A B) (v : Body (C × S) A B)
          → (∀ c sa → v (padₛ (c ,_) sa) ≈ₚ mapₚ (padₛ (c ,_)) (u sa))
          → (c : C) (sa : S × A)
          → iterₚ v (padₛ (c ,_) sa) ≈ₚ mapₚ (padₛ (c ,_)) (iterₚ u sa)
iterₚ-ctx u v h c = iterₚ-uniform u v (c ,_) (h c)
