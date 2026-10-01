{-# OPTIONS --safe --without-K --guardedness #-}

-- `Dₚ` is commutative up to `_≈ₚ_`.  The two orders of a pair share one budget
-- and agree only cofinally; what is exact is Fubini at two independent budgets
-- (`cum-fubini`, the analogue of `RationalDist.lookupᴰℚ-swap`), which the bind
-- sandwich turns into domination both ways.

open import Data.Bool.Base
open import Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties
open import Data.Sum.Base
open import Function.Base
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

module ProbabilisticLogic.Dp.Commutative where

private variable
  a : Level
  A B C : Set a

------------------------------------------------------------------------
-- Commutativity

pairₚ : Dₚ A → Dₚ B → Dₚ (A × B)
pairₚ d e = d >>=ₚ λ p → mapₚ (p ,_) e

pairₚ′ : Dₚ A → Dₚ B → Dₚ (A × B)
pairₚ′ d e = e >>=ₚ λ q → mapₚ (_, q) d

pairₚ-≼ : (d : Dₚ A) (e : Dₚ B) → pairₚ d e ≼ₚ pairₚ′ d e
pairₚ-≼ d e P nn n = n +ℕ suc n ,
  ≤-trans (>>=ₚ-boundA n d (λ p → mapₚ (p ,_) e) P nn)
  (≤-trans (cum-mono-P n d (λ p → cum n (mapₚ (p ,_) e) P) (λ p → cum n e (λ q → P (p , q)))
                       (λ p → mapₚ-≤ n (p ,_) e P nn))
  (≤-trans (≤-reflexive (cum-fubini n n d e (λ p q → P (p , q))))
  (≤-trans (≤-reflexive (cum-cong-P n e (λ q → cum n d (λ p → P (p , q)))
                                        (λ q → cum (suc n) (mapₚ (_, q) d) P)
                                        (λ q → sym (mapₚ-cum n (_, q) d P))))
           (>>=ₚ-boundB n (suc n) e (λ q → mapₚ (_, q) d) P nn))))

pairₚ′-≼ : (d : Dₚ A) (e : Dₚ B) → pairₚ′ d e ≼ₚ pairₚ d e
pairₚ′-≼ d e P nn n = n +ℕ suc n ,
  ≤-trans (>>=ₚ-boundA n e (λ q → mapₚ (_, q) d) P nn)
  (≤-trans (cum-mono-P n e (λ q → cum n (mapₚ (_, q) d) P) (λ q → cum n d (λ p → P (p , q)))
                       (λ q → mapₚ-≤ n (_, q) d P nn))
  (≤-trans (≤-reflexive (sym (cum-fubini n n d e (λ p q → P (p , q)))))
  (≤-trans (≤-reflexive (cum-cong-P n d (λ p → cum n e (λ q → P (p , q)))
                                        (λ p → cum (suc n) (mapₚ (p ,_) e) P)
                                        (λ p → sym (mapₚ-cum n (p ,_) e P))))
           (>>=ₚ-boundB n (suc n) d (λ p → mapₚ (p ,_) e) P nn))))

>>=ₚ-comm : (d : Dₚ A) (e : Dₚ B)
          → (d >>=ₚ λ p → e >>=ₚ λ q → returnₚ (p , q))
          ≈ₚ (e >>=ₚ λ q → d >>=ₚ λ p → returnₚ (p , q))
>>=ₚ-comm d e = pairₚ-≼ d e , pairₚ′-≼ d e

>>=ₚ-swap : (d : Dₚ A) (e : Dₚ B) (h : A → B → Dₚ C)
          → (d >>=ₚ λ p → e >>=ₚ λ q → h p q) ≈ₚ (e >>=ₚ λ q → d >>=ₚ λ p → h p q)
>>=ₚ-swap d e h =
      bindᶠ (λ p → bindᶠ (λ q → push (uncurry h) (p , q))
               ⟨≈⟩ ≈sym (>>=ₚ-assoc e (λ q → returnₚ (p , q)) (uncurry h)))
  ⟨≈⟩ ≈sym (>>=ₚ-assoc d (λ p → e >>=ₚ λ q → returnₚ (p , q)) (uncurry h))
  ⟨≈⟩ bindˣ (>>=ₚ-comm d e)
  ⟨≈⟩ >>=ₚ-assoc e (λ q → d >>=ₚ λ p → returnₚ (p , q)) (uncurry h)
  ⟨≈⟩ bindᶠ (λ q → >>=ₚ-assoc d (λ p → returnₚ (p , q)) (uncurry h)
               ⟨≈⟩ bindᶠ (λ p → >>=ₚ-identityˡ (p , q) (uncurry h)))
