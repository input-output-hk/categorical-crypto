{-# OPTIONS --safe --without-K --guardedness #-}

module ProbabilisticLogic.Dp.Positive.Transfer where

open import Data.Empty
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
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

private variable a : Level

module _ {S A B T C D : Set a} (u : Body S A B) (v : Body T C D)
  (k : S × A → T × C) (m : S × B → T × D)
  (hyp : ∀ sa → v (k sa) ≈₊ mapₚ (φ k m) (u sa))
  (P : T × D → ℚ) (nn : NNF P) where

  pull-nn : NNF (λ sb → P (m sb))
  pull-nn sb = nn (m sb)

  mutual
    forward : (n : ℕ) (sa : S × A)
            → 0ℚ ℚ.< cum n (iterₚ u sa) (λ sb → P (m sb)) → PositiveTest (iterₚ v (k sa)) P
    forward zero sa pos = ⊥-elim (<-irrefl refl pos)
    forward (suc n) sa pos =
      let test = Tᵗ u (λ sb → P (m sb)) n
          test-nn = Tᵗ-nn u (λ sb → P (m sb)) n pull-nn
          r , path , inner = positive-extract (suc n) (u sa) test test-nn
            (<-≤-trans pos (stepᵢ-boundA n u (u sa) (λ sb → P (m sb)) pull-nn))
          i , next = forward-next n r inner
          outer = positive-witness (λ r → Tᵗ v P i (φ k m r))
            (λ r → Tᵗ-nn v P i nn (φ k m r)) path next
          j , out = proj₂ (hyp sa) (Tᵗ v P i) (Tᵗ-nn v P i nn)
            (map-positive-to (φ k m) (u sa) (Tᵗ v P i) (Tᵗ-nn v P i nn) outer)
      in j + i , <-≤-trans out (stepᵢ-boundB j i v (v (k sa)) P nn)

    forward-next : (n : ℕ) (r : S × (B ⊎ A))
                 → 0ℚ ℚ.< Tᵗ u (λ sb → P (m sb)) n r
                 → ∃ λ i → 0ℚ ℚ.< Tᵗ v P i (φ k m r)
    forward-next n (s , inj₁ b) pos = 0 , pos
    forward-next n (s , inj₂ a) pos = forward n (s , a) pos

  mutual
    backward : (n : ℕ) (sa : S × A) → 0ℚ ℚ.< cum n (iterₚ v (k sa)) P
             → PositiveTest (iterₚ u sa) (λ sb → P (m sb))
    backward zero sa pos = ⊥-elim (<-irrefl refl pos)
    backward (suc n) sa pos =
      let test = Tᵗ v P n
          test-nn = Tᵗ-nn v P n nn
          outer = proj₁ (hyp sa) test test-nn
            (suc n , <-≤-trans pos (stepᵢ-boundA n v (v (k sa)) P nn))
          j , out = map-positive-from (φ k m) (u sa) test test-nn outer
          r , path , inner = positive-extract j (u sa) (λ r → test (φ k m r))
            (λ r → test-nn (φ k m r)) out
          result = bind-witness (u sa) (contᵢ u) (λ sb → P (m sb)) pull-nn path (backward-next n r inner)
      in positive-test-cong pull-nn (≈ₚ-sym (iterₚ u sa) (u sa >>=ₚ contᵢ u) (iterₚ-fix u sa)) result

    backward-next : (n : ℕ) (r : S × (B ⊎ A)) → 0ℚ ℚ.< Tᵗ v P n (φ k m r)
                  → PositiveTest (contᵢ u r) (λ sb → P (m sb))
    backward-next n (s , inj₁ b) pos = positive-witness (λ sb → P (m sb)) pull-nn (positive-return (s , b)) pos
    backward-next n (s , inj₂ a) pos = backward n (s , a) pos

iter-transfer : {S A B T C D : Set a} (u : Body S A B) (v : Body T C D)
  (k : S × A → T × C) (m : S × B → T × D)
  → (∀ sa → v (k sa) ≈₊ mapₚ (φ k m) (u sa))
  → (sa : S × A) → iterₚ v (k sa) ≈₊ mapₚ m (iterₚ u sa)
iter-transfer u v k m hyp sa =
  (λ P nn (n , pos) → map-positive-to m (iterₚ u sa) P nn (backward u v k m hyp P nn n sa pos)) ,
  λ P nn p → let n , pos = map-positive-from m (iterₚ u sa) P nn p
             in forward u v k m hyp P nn n sa pos
