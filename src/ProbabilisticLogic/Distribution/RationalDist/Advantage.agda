{-# OPTIONS --safe --without-K #-}

-- The distinguishing advantage between two partial verdict distributions: the
-- gap between their probabilities of answering `b`.
--
-- It is a pseudometric — symmetric, subadditive, and zero on `≈Mℚ`-equal
-- arguments.  `nothing` mass counts as neither verdict, `maybeℚ` sending it to
-- `0ℚ`, so at a FIXED `b` a diverging experiment moves the advantage the same
-- way a `¬ b` one does; observing both verdicts is what separates them
-- (proposal §1, `docs/kb/frontier/15-probabilistic-uc-model.typ`).  `adv⊥` is
-- the `true` reading, which is all a probability-of-event statement needs.

open import Data.Bool.Base
open import Data.Maybe.Base using (just)
open import Data.Rational
  renaming (_+_ to _+ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform using (bool→ℚ; indᵇ)

module ProbabilisticLogic.Distribution.RationalDist.Advantage where

advᵇ⊥ : Bool → Dist⊥ Bool → Dist⊥ Bool → ℚ
advᵇ⊥ b μ ν = ∣ Prᵇ⊥ b μ -ℚ Prᵇ⊥ b ν ∣ℚ

adv⊥ : Dist⊥ Bool → Dist⊥ Bool → ℚ
adv⊥ = advᵇ⊥ true

-- The pseudometric laws hold at each verdict separately, which is the form a
-- statement reading BOTH verdicts needs (`CategoricalCrypto.Protocol.Observe`'s
-- `_≈adv[_]_`, and the relation over it in `CategoricalCrypto.UC.Saturated`).
advᵇ⊥-refl : ∀ b μ → advᵇ⊥ b μ μ ≡ 0ℚ
advᵇ⊥-refl b μ = cong ∣_∣ℚ (+-inverseʳ (Prᵇ⊥ b μ))

advᵇ⊥-sym : ∀ b μ ν → advᵇ⊥ b μ ν ≡ advᵇ⊥ b ν μ
advᵇ⊥-sym b μ ν = trans (cong ∣_∣ℚ (neg-sub (Prᵇ⊥ b μ) (Prᵇ⊥ b ν))) (∣-p∣≡∣p∣ _)

advᵇ⊥-triangle : ∀ b μ ν ρ → advᵇ⊥ b μ ρ ≤ℚ advᵇ⊥ b μ ν +ℚ advᵇ⊥ b ν ρ
advᵇ⊥-triangle b μ ν ρ =
  subst (λ z → ∣ z ∣ℚ ≤ℚ advᵇ⊥ b μ ν +ℚ advᵇ⊥ b ν ρ)
        (telescope (Prᵇ⊥ b μ) (Prᵇ⊥ b ν) (Prᵇ⊥ b ρ))
        (∣p+q∣≤∣p∣+∣q∣ (Prᵇ⊥ b μ -ℚ Prᵇ⊥ b ν) (Prᵇ⊥ b ν -ℚ Prᵇ⊥ b ρ))

adv⊥-sym : ∀ μ ν → adv⊥ μ ν ≡ adv⊥ ν μ
adv⊥-sym = advᵇ⊥-sym true

adv⊥-triangle : ∀ μ ν ρ → adv⊥ μ ρ ≤ℚ adv⊥ μ ν +ℚ adv⊥ ν ρ
adv⊥-triangle = advᵇ⊥-triangle true

adv⊥-≈⇒0 : {μ ν : Dist⊥ Bool} → μ ≈Mℚ ν → adv⊥ μ ν ≡ 0ℚ
adv⊥-≈⇒0 {μ} = λ e → trans (cong (λ z → ∣ Pr₁⊥ μ -ℚ z ∣ℚ) (sym (e mb)))
                           (cong ∣_∣ℚ (+-inverseʳ (Pr₁⊥ μ)))

------------------------------------------------------------------------
-- Where the two readings coincide

-- An experiment with NO divergence mass answers `false` exactly when it does
-- not answer `true`, so both readings of the advantage are the same number.
-- This is what lets a one-sided concrete-security theorem be stated at the
-- two-sided `advᵇ⊥`.
private
  Prᵇ⊥-just : ∀ b (μ : Dist-ℚ Bool) → Prᵇ⊥ b (Dmap just μ) ≡ E μ (indᵇ b)
  Prᵇ⊥-just b μ = lookupᴰℚ-Dmap just μ (maybeℚ (indᵇ b))

  E-not : (μ : Dist-ℚ Bool) → E μ (indᵇ false) ≡ 1ℚ -ℚ Pr₁ μ
  E-not μ = trans (lookupᴰℚ-cong-P (entries μ) pt)
           (trans (E-sub μ (λ _ → 1ℚ) bool→ℚ) (cong (_-ℚ Pr₁ μ) (E-const μ 1ℚ)))
    where pt : ∀ x → bool→ℚ (not x) ≡ 1ℚ -ℚ bool→ℚ x
          pt true  = sym (+-inverseʳ 1ℚ)
          pt false = sym (+-identityʳ 1ℚ)

  swap-compl : ∀ a b → (1ℚ -ℚ a) -ℚ (1ℚ -ℚ b) ≡ b -ℚ a
  swap-compl a b = trans (cong ((1ℚ -ℚ a) +ℚ_) (sym (neg-sub b 1ℚ)))
                  (trans (+-comm (1ℚ -ℚ a) (b -ℚ 1ℚ)) (telescope b 1ℚ a))

advᵇ⊥-just : ∀ b (μ ν : Dist-ℚ Bool)
           → advᵇ⊥ b (Dmap just μ) (Dmap just ν) ≡ ∣ Pr₁ μ -ℚ Pr₁ ν ∣ℚ
advᵇ⊥-just true  μ ν = cong₂ (λ x y → ∣ x -ℚ y ∣ℚ) (Prᵇ⊥-just true μ) (Prᵇ⊥-just true ν)
advᵇ⊥-just false μ ν =
  trans (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ)
          (trans (Prᵇ⊥-just false μ) (E-not μ)) (trans (Prᵇ⊥-just false ν) (E-not ν)))
 (trans (cong ∣_∣ℚ (swap-compl (Pr₁ μ) (Pr₁ ν)))
 (trans (cong ∣_∣ℚ (neg-sub (Pr₁ ν) (Pr₁ μ))) (∣-p∣≡∣p∣ (Pr₁ μ -ℚ Pr₁ ν))))
