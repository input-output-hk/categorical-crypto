{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The inversion count as an explicit SUM over pairs, `invS`.
--
-- DESIGN: unlike the recursive (Lehmer) `inv` of `Inversions.agda` (whose
-- L1 `i=0` case is blocked because the two residuals peel value 0 from
-- different positions), `invS` counts inversion pairs directly.  A
-- generator `genFB i` (transposing the VALUES `i, i+1`) then flips exactly
-- one pair — the positions holding `i` and `i+1` — giving a uniform L1.
--
-- This file builds the bounded sum `sumF`, its bookkeeping lemmas, and
-- `invS`.
------------------------------------------------------------------------

module Categories.PermuteCoherence.InversionsSum where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc)
open import Data.Fin.Base using (Fin) renaming (suc to fsuc; zero to fz)
open import Data.Fin.Patterns using (0F)
open import Data.Fin.Properties using (suc-injective)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Fin.Properties using (_<?_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

import Data.Fin.Permutation as P
open import Categories.PermuteCoherence.FinBij using (FinBij)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- 1. Bounded sums over `Fin n`.

sumF : {n : ℕ} → (Fin n → ℕ) → ℕ
sumF {zero}  f = 0
sumF {suc n} f = f 0F + sumF (λ i → f (fsuc i))

-- Pointwise-equal functions have equal sums.
sumF-cong : {n : ℕ} {f g : Fin n → ℕ} → (∀ i → f i ≡ g i) → sumF f ≡ sumF g
sumF-cong {zero}  eq = refl
sumF-cong {suc n} eq = cong₂ _+_ (eq 0F) (sumF-cong (λ i → eq (fsuc i)))

-- A sum of pointwise sums is the sum of the parts.
sumF-+ : {n : ℕ} (f g : Fin n → ℕ) → sumF (λ i → f i + g i) ≡ sumF f + sumF g
sumF-+ {zero}  f g = refl
sumF-+ {suc n} f g =
  trans (cong (f 0F + g 0F +_) (sumF-+ (λ i → f (fsuc i)) (λ i → g (fsuc i))))
        (lemma (f 0F) (g 0F) (sumF (λ i → f (fsuc i))) (sumF (λ i → g (fsuc i))))
  where
  -- (a + b) + (s + t) ≡ (a + s) + (b + t)
  lemma : (a b s t : ℕ) → (a + b) + (s + t) ≡ (a + s) + (b + t)
  lemma a b s t =
    trans (+-assoc a b (s + t))
    (trans (cong (a +_) (trans (sym (+-assoc b s t))
                        (trans (cong (_+ t) (+-comm b s)) (+-assoc s b t))))
           (sym (+-assoc a s (b + t))))

-- If f, g agree off index k and f k = suc (g k), then sumF f = suc (sumF g).
sumF-step : {n : ℕ} (f g : Fin n → ℕ) (k : Fin n)
          → (∀ j → j ≢ k → f j ≡ g j) → f k ≡ suc (g k)
          → sumF f ≡ suc (sumF g)
sumF-step {suc n} f g 0F       off at0 =
  cong₂ _+_ at0 (sumF-cong (λ i → off (fsuc i) (λ ())))
sumF-step {suc n} f g (fsuc k) off atk =
  trans (cong₂ _+_ (off 0F (λ ()))
                   (sumF-step (λ i → f (fsuc i)) (λ i → g (fsuc i)) k
                              (λ j j≢k → off (fsuc j) (λ e → j≢k (suc-injective e))) atk))
        (+-suc (g 0F) (sumF (λ i → g (fsuc i))))

------------------------------------------------------------------------
-- 2. The inversion count as a double sum over position-pairs.

-- 1 on `true`, 0 on `false`.
1if : Bool → ℕ
1if true  = 1
1if false = 0

-- `invAt b x y = 1` iff `(x, y)` is an inversion of `b` (x < y but b x > b y).
invAt : FinBij (suc n) (suc n) → Fin (suc n) → Fin (suc n) → ℕ
invAt b x y = 1if (⌊ x <? y ⌋ ∧ ⌊ (b P.⟨$⟩ʳ y) <? (b P.⟨$⟩ʳ x) ⌋)

invS : FinBij (suc n) (suc n) → ℕ
invS b = sumF (λ x → sumF (λ y → invAt b x y))
