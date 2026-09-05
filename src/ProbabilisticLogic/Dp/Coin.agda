{-# OPTIONS --safe --without-K --guardedness #-}

-- A finite rational distribution on `Bool` as a single biased coin.  `Dₚ`'s
-- step is deliberately binary (see its header), so a `Dist-ℚ Bool` — a list of
-- weighted entries, possibly with repeats — enters the delay monad only through
-- its two aggregate masses, which is exactly what `choiceₚ`'s invariants ask
-- for.  `coinₚ-cum` is the agreement: the coin scores every test the
-- distribution does, exactly, at any budget past the two branch steps.

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties as ℚP
open import Data.Rational.Properties.Ext
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist

open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp

module ProbabilisticLogic.Dp.Coin where

private variable P : Bool → ℚ

-- The indicator of `false`; `bool→ℚ` is the indicator of `true`.
ind˘ : Bool → ℚ
ind˘ b = bool→ℚ (not b)

private
  0≤ind : ∀ b → 0ℚ ℚ.≤ bool→ℚ b
  0≤ind true  = 0≤1ℚ
  0≤ind false = ≤-refl

  0≤E : (μ : Dist-ℚ Bool) → (∀ b → 0ℚ ℚ.≤ P b) → 0ℚ ℚ.≤ E μ P
  0≤E {P} μ nn = ≤-trans (≤-reflexive (sym (E-const μ 0ℚ))) (E-mono μ (λ _ → 0ℚ) P nn)

  -- The two masses add to one because the two indicators do, pointwise.
  masses-1 : (μ : Dist-ℚ Bool) → E μ bool→ℚ ℚ.+ E μ ind˘ ≡ 1ℚ
  masses-1 μ = trans (sym (lookupᴰℚ-+ (entries μ) bool→ℚ ind˘))
                     (trans (lookupᴰℚ-cong-P (entries μ) sum-1) (E-const μ 1ℚ))
    where sum-1 : ∀ b → bool→ℚ b ℚ.+ ind˘ b ≡ 1ℚ
          sum-1 true  = refl
          sum-1 false = refl

coinₚ : Dist-ℚ Bool → Dₚ Bool
coinₚ μ = choiceₚ (E μ bool→ℚ) (E μ ind˘)
                  (0≤E μ 0≤ind) (0≤E μ (λ b → 0≤ind (not b)))
                  (masses-1 μ) (returnₚ true) (returnₚ false)

-- Both branches spend one delay step, so the budget is `suc (suc n)`.
coinₚ-cum : (μ : Dist-ℚ Bool) (n : ℕ) (P : Bool → ℚ)
          → cum (suc (suc n)) (coinₚ μ) P ≡ E μ P
coinₚ-cum μ n P = trans branches (trans (cong₂ ℚ._+_ (pull bool→ℚ _) (pull ind˘ _))
                                        (trans (sym (lookupᴰℚ-+ (entries μ) _ _))
                                               (lookupᴰℚ-cong-P (entries μ) split)))
  where
    branches : cum (suc (suc n)) (coinₚ μ) P
             ≡ E μ bool→ℚ ℚ.* P true ℚ.+ E μ ind˘ ℚ.* P false
    branches = cong₂ ℚ._+_ (cong (E μ bool→ℚ ℚ.*_) (returnₚ-cum n true P))
                           (cong (E μ ind˘ ℚ.*_) (returnₚ-cum n false P))

    pull : (Q : Bool → ℚ) (x : ℚ)
         → E μ Q ℚ.* x ≡ lookupᴰℚ (entries μ) (λ b → Q b ℚ.* x)
    pull Q x = trans (ℚP.*-comm (E μ Q) x)
                     (trans (sym (lookupᴰℚ-*ₗ x (entries μ) Q))
                            (lookupᴰℚ-cong-P (entries μ) (λ b → ℚP.*-comm x (Q b))))

    split : ∀ b → bool→ℚ b ℚ.* P true ℚ.+ ind˘ b ℚ.* P false ≡ P b
    split true  = trans (cong₂ ℚ._+_ (ℚP.*-identityˡ (P true)) (ℚP.*-zeroˡ (P false)))
                        (ℚP.+-identityʳ (P true))
    split false = trans (cong₂ ℚ._+_ (ℚP.*-zeroˡ (P true)) (ℚP.*-identityˡ (P false)))
                        (ℚP.+-identityˡ (P false))
