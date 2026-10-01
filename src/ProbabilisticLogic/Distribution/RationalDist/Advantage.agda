{-# OPTIONS --safe --without-K #-}

-- The distinguishing advantage between two partial verdict distributions at
-- verdict `b`.  `nothing` scores 0 under either indicator, so both verdicts are
-- read (see `ProbabilisticLogic.Dp.Advantage`'s header); `adv⊥` is the `true`
-- reading, which is all a probability-of-event statement needs.

open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.Rational renaming (_+_ to _+ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform

module ProbabilisticLogic.Distribution.RationalDist.Advantage where

advᵇ⊥ : Bool → Dist⊥ Bool → Dist⊥ Bool → ℚ
advᵇ⊥ b μ ν = ∣ Prᵇ⊥ b μ -ℚ Prᵇ⊥ b ν ∣ℚ

adv⊥ : Dist⊥ Bool → Dist⊥ Bool → ℚ
adv⊥ = advᵇ⊥ true

advᵇ⊥-sym : ∀ b μ ν → advᵇ⊥ b μ ν ≡ advᵇ⊥ b ν μ
advᵇ⊥-sym b μ ν = ∣-∣-comm (Prᵇ⊥ b μ) (Prᵇ⊥ b ν)

advᵇ⊥-triangle : ∀ b μ ν ρ → advᵇ⊥ b μ ρ ≤ℚ advᵇ⊥ b μ ν +ℚ advᵇ⊥ b ν ρ
advᵇ⊥-triangle b μ ν ρ = ∣-∣-triangle (Prᵇ⊥ b μ) (Prᵇ⊥ b ν) (Prᵇ⊥ b ρ)

adv⊥-sym : ∀ μ ν → adv⊥ μ ν ≡ adv⊥ ν μ
adv⊥-sym = advᵇ⊥-sym true

adv⊥-triangle : ∀ μ ν ρ → adv⊥ μ ρ ≤ℚ adv⊥ μ ν +ℚ adv⊥ ν ρ
adv⊥-triangle = advᵇ⊥-triangle true

adv⊥-≈⇒0 : {μ ν : Dist⊥ Bool} → μ ≈Mℚ ν → adv⊥ μ ν ≡ 0ℚ
adv⊥-≈⇒0 {μ} e = trans (cong (λ z → ∣ Pr₁⊥ μ -ℚ z ∣ℚ) (sym (e mb)))
                       (∣x-x∣≡0 (Pr₁⊥ μ))

-- With no divergence mass the `false` reading is the complement of the `true`
-- one, so a one-sided bound can be stated at the two-sided `advᵇ⊥`.
advᵇ⊥-just : ∀ b (μ ν : Dist-ℚ Bool)
           → advᵇ⊥ b (Dmap just μ) (Dmap just ν) ≡ ∣ Pr₁ μ -ℚ Pr₁ ν ∣ℚ
advᵇ⊥-just true  μ ν = cong₂ (λ x y → ∣ x -ℚ y ∣ℚ) (Eⱼ μ (indᵇ true)) (Eⱼ ν (indᵇ true))
advᵇ⊥-just false μ ν =
  trans (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ)
          (trans (Eⱼ μ (indᵇ false)) (E-not μ)) (trans (Eⱼ ν (indᵇ false)) (E-not ν)))
 (trans (cong ∣_∣ℚ (1-x-[1-y] (Pr₁ μ) (Pr₁ ν))) (∣-∣-comm (Pr₁ ν) (Pr₁ μ)))
