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
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.Fin.Base using (Fin; punchIn) renaming (suc to fsuc; zero to fz)
open import Data.Fin.Patterns using (0F)
open import Data.Fin.Properties using (punchInᵢ≢i)
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

-- The constantly-zero sum vanishes.
sumF-const0 : {N : ℕ} → sumF {N} (λ _ → 0) ≡ 0
sumF-const0 {zero}  = refl
sumF-const0 {suc N} = sumF-const0 {N}

-- Pull one index out of a `Fin (suc N)`-sum:
--   sumF g ≡ g m + sumF (g ∘ punchIn m)  (`punchIn m` enumerates ∖ {m}).
sumF-punch : {N : ℕ} (g : Fin (suc N) → ℕ) (m : Fin (suc N))
           → sumF g ≡ g m + sumF (λ j → g (punchIn m j))
sumF-punch {zero}  g 0F = refl
sumF-punch {suc N} g 0F = refl
sumF-punch {suc N} g (fsuc m) =
  trans (cong (g 0F +_) (sumF-punch (λ j → g (fsuc j)) m))
        (lemma (g 0F) (g (fsuc m)) (sumF (λ j → g (fsuc (punchIn m j)))))
  where
  lemma : (a c S : ℕ) → a + (c + S) ≡ c + (a + S)
  lemma a c S =
    trans (sym (+-assoc a c S))
          (trans (cong (_+ S) (+-comm a c)) (+-assoc c a S))

-- If f, g agree off index k and f k = suc (g k), then sumF f = suc (sumF g).
sumF-step : {n : ℕ} (f g : Fin n → ℕ) (k : Fin n)
          → (∀ j → j ≢ k → f j ≡ g j) → f k ≡ suc (g k)
          → sumF f ≡ suc (sumF g)
sumF-step {suc n} f g k off atk =
  trans (sumF-punch f k)
  (trans (cong₂ _+_ atk (sumF-cong (λ j → off (punchIn k j) (punchInᵢ≢i k j))))
         (cong suc (sym (sumF-punch g k))))

-- Two nested `sumF-step`s: if the matrices `F`, `G` agree everywhere
-- except a single cell `(x₀, y₀)` where `F x₀ y₀ = suc (G x₀ y₀)`, then
-- their double sums differ by one.
double-step :
    {N : ℕ} (F G : Fin N → Fin N → ℕ) (x₀ y₀ : Fin N)
  → (∀ x → x ≢ x₀ → ∀ y → F x y ≡ G x y)
  → (∀ y → y ≢ y₀ → F x₀ y ≡ G x₀ y)
  → F x₀ y₀ ≡ suc (G x₀ y₀)
  → sumF (λ x → sumF (F x)) ≡ suc (sumF (λ x → sumF (G x)))
double-step F G x₀ y₀ offRow inRow atCell =
  sumF-step (λ x → sumF (F x)) (λ x → sumF (G x)) x₀
    (λ x x≢x₀ → sumF-cong (offRow x x≢x₀))
    (sumF-step (F x₀) (G x₀) y₀ inRow atCell)

------------------------------------------------------------------------
-- 2. The inversion count as a double sum over position-pairs.

-- 1 on `true`, 0 on `false`.
1if : Bool → ℕ
1if true  = 1
1if false = 0

-- `1if (p ∧ _)` only depends on the second conjunct when `p ≡ true`.
1if-∧-cong : (p : Bool) {q₁ q₂ : Bool} → (p ≡ true → q₁ ≡ q₂)
           → 1if (p ∧ q₁) ≡ 1if (p ∧ q₂)
1if-∧-cong true  h = cong (λ z → 1if (true ∧ z)) (h refl)
1if-∧-cong false _ = refl

-- `invAt b x y = 1` iff `(x, y)` is an inversion of `b` (x < y but b x > b y).
invAt : FinBij (suc n) (suc n) → Fin (suc n) → Fin (suc n) → ℕ
invAt b x y = 1if (⌊ x <? y ⌋ ∧ ⌊ (b P.⟨$⟩ʳ y) <? (b P.⟨$⟩ʳ x) ⌋)

invS : FinBij (suc n) (suc n) → ℕ
invS b = sumF (λ x → sumF (λ y → invAt b x y))
