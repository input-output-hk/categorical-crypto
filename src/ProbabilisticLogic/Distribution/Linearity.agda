{-# OPTIONS --safe --without-K #-}

-- Generic linearity for weighted assoc-lists, parametric in the
-- weight semiring.

open import Algebra using (CommutativeSemiring)

module ProbabilisticLogic.Distribution.Linearity {c ℓ} (R : CommutativeSemiring c ℓ) where

open import Level
open import Data.Product
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Data.List as L
import Data.List.Properties as LP
open import Relation.Binary.PropositionalEquality using (_≡_)

open CommutativeSemiring R renaming (Carrier to W)
open ≈-Reasoning setoid

open import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup
  using () renaming (interchange to +-swap-middle)

open import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup
  using (x∙yz≈y∙xz)

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set ℓ₁
    B : Set ℓ₂

------------------------------------------------------------------------
-- Lookup on assoc lists: `Σᵢ wᵢ · P(aᵢ)`.
--
-- This is a little trick to avoid requiring decidable equality

lookup-L : List (W × A) → (A → W) → W
lookup-L []             _ = 0#
lookup-L ((w , a) ∷ xs) P = w * P a + lookup-L xs P

------------------------------------------------------------------------
-- Pointwise weight scaling.

scaleL : W → List (W × A) → List (W × A)
scaleL w = L.map (λ (w′ , a) → (w * w′ , a))

scaleL-++ : ∀ (w : W) (xs ys : List (W × A))
          → scaleL w (xs ++ ys) ≡ scaleL w xs ++ scaleL w ys
scaleL-++ w xs ys = LP.map-++ _ xs ys

------------------------------------------------------------------------
-- Linearity lemmas.

lookup-L-++ : (xs ys : List (W × A)) (P : A → W)
            → lookup-L (xs ++ ys) P ≈ lookup-L xs P + lookup-L ys P
lookup-L-++ []             ys P = sym (+-identityˡ _)
lookup-L-++ ((w , a) ∷ xs) ys P = begin
  w * P a + lookup-L (xs ++ ys) P
    ≈⟨ +-congˡ (lookup-L-++ xs ys P) ⟩
  w * P a + (lookup-L xs P + lookup-L ys P)
    ≈⟨ sym (+-assoc _ _ _) ⟩
  (w * P a + lookup-L xs P) + lookup-L ys P ∎

lookup-L-scaleL : (w : W) (xs : List (W × A)) (P : A → W)
                → lookup-L (scaleL w xs) P ≈ w * lookup-L xs P
lookup-L-scaleL w []              P = sym (zeroʳ w)
lookup-L-scaleL w ((w′ , a) ∷ xs) P = begin
  (w * w′) * P a + lookup-L (scaleL w xs) P
    ≈⟨ +-cong (*-assoc w w′ (P a)) (lookup-L-scaleL w xs P) ⟩
  w * (w′ * P a) + w * lookup-L xs P
    ≈⟨ sym (distribˡ w _ _) ⟩
  w * (w′ * P a + lookup-L xs P) ∎

lookup-L-cong-P : (xs : List (W × A)) {P Q : A → W}
                → (∀ a → P a ≈ Q a) → lookup-L xs P ≈ lookup-L xs Q
lookup-L-cong-P []             P≈Q = refl
lookup-L-cong-P ((w , a) ∷ xs) P≈Q =
  +-cong (*-congˡ (P≈Q a)) (lookup-L-cong-P xs P≈Q)

lookup-L-zero : (xs : List (W × A)) → lookup-L xs (λ _ → 0#) ≈ 0#
lookup-L-zero []             = refl
lookup-L-zero ((w , a) ∷ xs) = begin
  w * 0# + lookup-L xs (λ _ → 0#)
    ≈⟨ +-cong (zeroʳ w) (lookup-L-zero xs) ⟩
  0# + 0#
    ≈⟨ +-identityˡ _ ⟩
  0# ∎

lookup-L-+ : (xs : List (W × A)) (P Q : A → W)
           → lookup-L xs (λ a → P a + Q a) ≈ lookup-L xs P + lookup-L xs Q
lookup-L-+ []             P Q = sym (+-identityˡ _)
lookup-L-+ ((w , a) ∷ xs) P Q = begin
  w * (P a + Q a) + lookup-L xs (λ a′ → P a′ + Q a′)
    ≈⟨ +-cong (distribˡ w _ _) (lookup-L-+ xs P Q) ⟩
  (w * P a + w * Q a) + (lookup-L xs P + lookup-L xs Q)
    ≈⟨ +-swap-middle _ _ _ _ ⟩
  (w * P a + lookup-L xs P) + (w * Q a + lookup-L xs Q) ∎

lookup-L-*ₗ : (c′ : W) (xs : List (W × A)) (P : A → W)
            → lookup-L xs (λ a → c′ * P a) ≈ c′ * lookup-L xs P
lookup-L-*ₗ c′ []             P = sym (zeroʳ c′)
lookup-L-*ₗ c′ ((w , a) ∷ xs) P = begin
  w * (c′ * P a) + lookup-L xs (λ a′ → c′ * P a′)
    ≈⟨ +-cong (x∙yz≈y∙xz w c′ (P a)) (lookup-L-*ₗ c′ xs P) ⟩
  c′ * (w * P a) + c′ * lookup-L xs P
    ≈⟨ sym (distribˡ c′ _ _) ⟩
  c′ * (w * P a + lookup-L xs P) ∎

------------------------------------------------------------------------
-- Total mass of a list.

mass-L : List (W × A) → W
mass-L xs = lookup-L xs (λ _ → 1#)

mass-L-++ : (xs ys : List (W × A))
          → mass-L (xs ++ ys) ≈ mass-L xs + mass-L ys
mass-L-++ xs ys = lookup-L-++ xs ys (λ _ → 1#)

mass-L-scale : (w : W) (xs : List (W × A))
             → mass-L (scaleL w xs) ≈ w * mass-L xs
mass-L-scale w xs = lookup-L-scaleL w xs (λ _ → 1#)

-- `lookup-L` against a constant test `λ _ → c` factors as `mass-L * c`.
-- Used by callers that need to discharge `discard`-style identities
-- where the kernel value is independent of the sample.
lookup-L-const : (xs : List (W × A)) (c : W)
               → lookup-L xs (λ _ → c) ≈ mass-L xs * c
lookup-L-const []             c = sym (zeroˡ c)
lookup-L-const ((w , a) ∷ xs) c = begin
  w * c + lookup-L xs (λ _ → c)
    ≈⟨ +-congˡ (lookup-L-const xs c) ⟩
  w * c + mass-L xs * c
    ≈⟨ +-congʳ (*-congʳ (sym (*-identityʳ w))) ⟩
  (w * 1#) * c + mass-L xs * c
    ≈⟨ sym (distribʳ c (w * 1#) (mass-L xs)) ⟩
  (w * 1# + mass-L xs) * c ∎

------------------------------------------------------------------------
-- Bind / Fubini.
--
-- We don't depend on `NE.List⁺`'s monad structure here; the concrete
-- modules unfold `NE.concatMap` into `L.concatMap` via the
-- `toList-concatMap-NE` lemma local to each, and feed us the resulting
-- `List`-level expression.

lookup-L-concatMap-scaleL :
    (k : A → List (W × B)) (P : B → W) (xs : List (W × A))
  → lookup-L (L.concatMap (λ (w , a) → scaleL w (k a)) xs) P
  ≈ lookup-L xs (λ a → lookup-L (k a) P)
lookup-L-concatMap-scaleL k P []             = refl
lookup-L-concatMap-scaleL k P ((w , a) ∷ xs) = begin
  lookup-L (scaleL w (k a) ++ L.concatMap _ xs) P
    ≈⟨ lookup-L-++ (scaleL w (k a)) _ P ⟩
  lookup-L (scaleL w (k a)) P + lookup-L (L.concatMap _ xs) P
    ≈⟨ +-cong (lookup-L-scaleL w (k a) P)
              (lookup-L-concatMap-scaleL k P xs) ⟩
  w * lookup-L (k a) P + lookup-L xs (λ a′ → lookup-L (k a′) P) ∎

-- Fubini on lists: swap the order of two nested `lookup-L`s.
lookup-L-swap : (xs : List (W × A)) (ys : List (W × B))
                (P : A → B → W)
              → lookup-L xs (λ x → lookup-L ys (P x))
              ≈ lookup-L ys (λ y → lookup-L xs (λ x → P x y))
lookup-L-swap []             ys P = sym (lookup-L-zero ys)
lookup-L-swap ((w , x) ∷ xs) ys P = begin
  w * lookup-L ys (P x) + lookup-L xs (λ x′ → lookup-L ys (P x′))
    ≈⟨ +-congˡ (lookup-L-swap xs ys P) ⟩
  w * lookup-L ys (P x) + lookup-L ys (λ y → lookup-L xs (λ x′ → P x′ y))
    ≈⟨ +-congʳ (sym (lookup-L-*ₗ w ys (P x))) ⟩
  lookup-L ys (λ y → w * P x y) + lookup-L ys (λ y → lookup-L xs (λ x′ → P x′ y))
    ≈⟨ sym (lookup-L-+ ys (λ y → w * P x y) (λ y → lookup-L xs (λ x′ → P x′ y))) ⟩
  lookup-L ys (λ y → w * P x y + lookup-L xs (λ x′ → P x′ y)) ∎
