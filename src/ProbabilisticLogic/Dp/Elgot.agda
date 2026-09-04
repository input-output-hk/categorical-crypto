{-# OPTIONS --safe --without-K --guardedness #-}

-- Uniformity and the context law for `iterₚ`, and the single entry point for the
-- iteration-law set: this module re-exports `iterₚ`, `iterₚ-cong`, `iterₚ-fix`,
-- `iterₚ-transfer`, `iterₚ-out` and `iterₚ-codiagonal`, so a consumer of Elgot
-- iteration at `Dₚ` needs this import alone.
--
-- Uniformity holds along an ARBITRARY pure state map `θ : S → S′`, with no
-- invertibility, and the context law is its `θ = (c ,_)` instance, so the latter
-- consumes no separate proof.  The one wrinkle is bureaucratic: `φ k m` case-splits
-- on the `⊎`-summand while a padded state map does not, so the two agree pointwise
-- but not as terms; `mapₚ-fn` bridges that.

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational using (ℚ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘′_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Commutative using (cum-cong-P)
open import ProbabilisticLogic.Dp.Iter
import ProbabilisticLogic.Dp.Iter.Codiagonal
import ProbabilisticLogic.Dp.Iter.Out
import ProbabilisticLogic.Dp.Iter.Transfer

module ProbabilisticLogic.Dp.Elgot where

-- Object variables are bound explicitly in every signature below: the `where`
-- blocks mention them, and a `private variable` there re-generalizes at a fresh
-- level.
private variable ℓ : Level

open ProbabilisticLogic.Dp.Iter public using (iterₚ; iterₚ-cong; iterₚ-fix)
open ProbabilisticLogic.Dp.Iter.Codiagonal public using (iterₚ-codiagonal)
open ProbabilisticLogic.Dp.Iter.Out public using (iterₚ-out)
open ProbabilisticLogic.Dp.Iter.Transfer public using (iterₚ-transfer)

------------------------------------------------------------------------
-- `mapₚ` in its function argument

mapₚ-fn-cum : {A B : Set ℓ} (n : ℕ) (h h′ : A → B) (d : Dₚ A) (P : B → ℚ)
            → (∀ p → h p ≡ h′ p) → cum n (mapₚ h d) P ≡ cum n (mapₚ h′ d) P
mapₚ-fn-cum zero    h h′ d P eq = refl
mapₚ-fn-cum (suc n) h h′ d P eq =
  trans (mapₚ-cum n h d P)
        (trans (cum-cong-P n d (P ∘′ h) (P ∘′ h′) (λ p → cong P (eq p)))
               (sym (mapₚ-cum n h′ d P)))

mapₚ-fn : {A B : Set ℓ} (h h′ : A → B) (d : Dₚ A)
        → (∀ p → h p ≡ h′ p) → mapₚ h d ≈ₚ mapₚ h′ d
mapₚ-fn h h′ d eq =
  exact⇒≈ₚ (mapₚ h d) (mapₚ h′ d) λ P n → mapₚ-fn-cum n h h′ d P eq

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
              (mapₚ-fn (padₛ θ) (φ (padₛ θ) (padₛ θ)) (u sa′) (λ r → sym (φ-padₛ θ r)))

iterₚ-ctx : {C S A B : Set ℓ} (u : Body S A B) (v : Body (C × S) A B)
          → (∀ c sa → v (padₛ (c ,_) sa) ≈ₚ mapₚ (padₛ (c ,_)) (u sa))
          → (c : C) (sa : S × A)
          → iterₚ v (padₛ (c ,_) sa) ≈ₚ mapₚ (padₛ (c ,_)) (iterₚ u sa)
iterₚ-ctx u v h c = iterₚ-uniform u v (c ,_) (h c)
