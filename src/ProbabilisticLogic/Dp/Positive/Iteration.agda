{-# OPTIONS --safe --without-K --guardedness #-}

module ProbabilisticLogic.Dp.Positive.Iteration where

open import Data.Empty
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties
open import Data.Sum.Base
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Paths
open import ProbabilisticLogic.Dp.Positive.Monad

private variable
  a : Level
  S A B : Set a

mutual
  iter-positive-to : (n : ℕ) (u v : Body S A B) → (∀ sa → u sa ≼₊ v sa)
                   → (sa : S × A) (P : S × B → ℚ) → NNF P
                   → 0ℚ ℚ.< cum n (iterₚ u sa) P → PositiveTest (iterₚ v sa) P
  iter-positive-to zero u v uv sa P nn pos = ⊥-elim (<-irrefl refl pos)
  iter-positive-to (suc n) u v uv sa P nn pos =
    let test = Tᵗ u P n
        test-nn = Tᵗ-nn u P n nn
        m , outer = uv sa test test-nn
          (suc n , <-≤-trans pos (stepᵢ-boundA n u (u sa) P nn))
        r , path , inner = positive-extract m (v sa) test test-nn outer
        result = bind-witness (v sa) (contᵢ v) P nn path (continue-positive n u v uv P nn r inner)
    in positive-test-cong nn (≈ₚ-sym (iterₚ v sa) (v sa >>=ₚ contᵢ v) (iterₚ-fix v sa)) result

  continue-positive : (n : ℕ) (u v : Body S A B) → (∀ sa → u sa ≼₊ v sa)
                     → (P : S × B → ℚ) → NNF P → (r : S × (B ⊎ A))
                     → 0ℚ ℚ.< Tᵗ u P n r → PositiveTest (contᵢ v r) P
  continue-positive n u v uv P nn (s , inj₁ b) pos =
    positive-witness P nn (positive-return (s , b)) pos
  continue-positive n u v uv P nn (s , inj₂ a) pos = iter-positive-to n u v uv (s , a) P nn pos

iter-cong : (u v : Body S A B) → (∀ sa → u sa ≈₊ v sa) → (sa : S × A)
          → iterₚ u sa ≈₊ iterₚ v sa
iter-cong u v uv sa =
  (λ P nn (n , pos) → iter-positive-to n u v (λ sa → proj₁ (uv sa)) sa P nn pos) ,
  λ P nn (n , pos) → iter-positive-to n v u (λ sa → proj₂ (uv sa)) sa P nn pos
