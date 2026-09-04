{-# OPTIONS --safe --without-K #-}

-- The distinguishing advantage between two partial verdict distributions: the
-- gap between their probabilities of answering `true`.
--
-- It is a pseudometric — symmetric, subadditive, and zero on `≈Mℚ`-equal
-- arguments.  `nothing` mass counts as neither verdict, `mb` sending it to
-- `0ℚ`, so a diverging experiment moves the advantage the same way a `false`
-- one does.

open import Data.Bool.Base using (Bool)
open import Data.Rational using (ℚ; 0ℚ)
  renaming (_+_ to _+ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (+-inverseʳ; ∣-p∣≡∣p∣; ∣p+q∣≤∣p∣+∣q∣)
open import Data.Rational.Properties.Ext using (neg-sub; telescope)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; sym; trans)

open import ProbabilisticLogic.Distribution.RationalDist using (_≈Mℚ_)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (Pr₁⊥; mb)
open import ProbabilisticLogic.Distribution.RationalDist.Partial using (Dist⊥)

module ProbabilisticLogic.Distribution.RationalDist.Advantage where

adv⊥ : Dist⊥ Bool → Dist⊥ Bool → ℚ
adv⊥ μ ν = ∣ Pr₁⊥ μ -ℚ Pr₁⊥ ν ∣ℚ

adv⊥-sym : ∀ μ ν → adv⊥ μ ν ≡ adv⊥ ν μ
adv⊥-sym μ ν = trans (cong ∣_∣ℚ (neg-sub (Pr₁⊥ μ) (Pr₁⊥ ν))) (∣-p∣≡∣p∣ _)

adv⊥-triangle : ∀ μ ν ρ → adv⊥ μ ρ ≤ℚ adv⊥ μ ν +ℚ adv⊥ ν ρ
adv⊥-triangle μ ν ρ =
  subst (λ z → ∣ z ∣ℚ ≤ℚ adv⊥ μ ν +ℚ adv⊥ ν ρ)
        (telescope (Pr₁⊥ μ) (Pr₁⊥ ν) (Pr₁⊥ ρ))
        (∣p+q∣≤∣p∣+∣q∣ (Pr₁⊥ μ -ℚ Pr₁⊥ ν) (Pr₁⊥ ν -ℚ Pr₁⊥ ρ))

adv⊥-≈⇒0 : {μ ν : Dist⊥ Bool} → μ ≈Mℚ ν → adv⊥ μ ν ≡ 0ℚ
adv⊥-≈⇒0 {μ} = λ e → trans (cong (λ z → ∣ Pr₁⊥ μ -ℚ z ∣ℚ) (sym (e mb)))
                           (cong ∣_∣ℚ (+-inverseʳ (Pr₁⊥ μ)))
