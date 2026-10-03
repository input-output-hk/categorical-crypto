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

pair-≼ : (f : A → B → C) (d : Dₚ A) (e : Dₚ B)
       → (d >>=ₚ λ p → mapₚ (f p) e) ≼ₚ (e >>=ₚ λ q → mapₚ (λ p → f p q) d)
pair-≼ f d e P nn n = n +ℕ suc n ,
  ≤-trans (>>=ₚ-boundA n d (λ p → mapₚ (f p) e) P nn)
  (≤-trans (cum-mono-P n d (λ p → cum n (mapₚ (f p) e) P) (λ p → cum n e (λ q → P (f p q)))
                       (λ p → mapₚ-≤ n (f p) e P nn))
  (≤-trans (≤-reflexive (cum-fubini n n d e (λ p q → P (f p q))))
  (≤-trans (≤-reflexive (cum-cong-P n e (λ q → cum n d (λ p → P (f p q)))
                                        (λ q → cum (suc n) (mapₚ (λ p → f p q) d) P)
                                        (λ q → sym (mapₚ-cum n (λ p → f p q) d P))))
           (>>=ₚ-boundB n (suc n) e (λ q → mapₚ (λ p → f p q) d) P nn))))

>>=ₚ-comm : (d : Dₚ A) (e : Dₚ B)
          → (d >>=ₚ λ p → e >>=ₚ λ q → returnₚ (p , q))
          ≈ₚ (e >>=ₚ λ q → d >>=ₚ λ p → returnₚ (p , q))
>>=ₚ-comm d e = pair-≼ _,_ d e , pair-≼ (λ q p → p , q) e d

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
