{-# OPTIONS --safe --without-K --guardedness #-}

-- `Supp-iterₚ`: a loop's depth-`n` support, from an invariant `J` of the loop
-- states and an exit predicate `Ψ` that every turn of the body lands in.  A
-- turn re-enters the body one step down (`tagᵢ`), so the induction is on the
-- budget alone and no coinduction is needed.

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Level using (Level)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter

module ProbabilisticLogic.Dp.Iter.Supp where

private variable
  ℓ ℓ′ : Level
  S A B : Set ℓ

-- Where a turn may land: an exit satisfying `Ψ`, or a loop state satisfying `J`.
Turn : (S × A → Set ℓ′) → (S × B → Set ℓ′) → S × (B ⊎ A) → Set ℓ′
Turn J Ψ (s , inj₁ y) = Ψ (s , y)
Turn J Ψ (s , inj₂ x) = J (s , x)

module _ {u : Body S A B} {J : S × A → Set ℓ′} {Ψ : S × B → Set ℓ′}
         (body : ∀ {sa} → J sa → ∀ n → Supp n (u sa) (Turn J Ψ)) where

  mutual
    Supp-stepᵢ : (n : ℕ) (x : Dₚ (S × (B ⊎ A))) → Supp n x (Turn J Ψ) → Supp n (stepᵢ u x) Ψ
    Supp-stepᵢ zero    _ _         = tt
    Supp-stepᵢ (suc n) x (s₁ , s₂) = SuppL-tagᵢ n (br x true) s₁ , SuppL-tagᵢ n (br x false) s₂

    SuppL-tagᵢ : (n : ℕ) (y : (S × (B ⊎ A)) ⊎ Dₚ (S × (B ⊎ A)))
               → SuppL n y (Turn J Ψ) → SuppL n (tagᵢ u y) Ψ
    SuppL-tagᵢ n (inj₁ (_ , inj₁ _)) h = h
    SuppL-tagᵢ n (inj₁ (s , inj₂ x)) h = Supp-stepᵢ n (u (s , x)) (body h n)
    SuppL-tagᵢ n (inj₂ x′)           h = Supp-stepᵢ n x′ h

  Supp-iterₚ : ∀ {sa} → J sa → ∀ n → Supp n (iterₚ u sa) Ψ
  Supp-iterₚ j n = Supp-stepᵢ n _ (body j n)
