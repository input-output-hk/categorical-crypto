{-# OPTIONS --safe --without-K --guardedness #-}

module ProbabilisticLogic.Dp.Positive.Examples where

open import Data.Bool.Base
open import Data.Empty
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; ½)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (toWitness; toWitnessFalse)
open import Relation.Nullary.Negation

open import ProbabilisticLogic.Distribution.Uniform using (indᵇ; indᵇ-nn)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Paths
open import ProbabilisticLogic.Dp.Positive.Monad

¼ ¾ ⅛ : ℚ
¼ = (+ 1) ℚ./ 4
¾ = (+ 3) ℚ./ 4
⅛ = (+ 1) ℚ./ 8

half-positive : 0ℚ ℚ.< ½
half-positive = toWitness {a? = 0ℚ ℚ.<? ½} tt
quarter-positive : 0ℚ ℚ.< ¼
quarter-positive = toWitness {a? = 0ℚ ℚ.<? ¼} tt
three-quarter-positive : 0ℚ ℚ.< ¾
three-quarter-positive = toWitness {a? = 0ℚ ℚ.<? ¾} tt
eighth-positive : 0ℚ ℚ.< ⅛
eighth-positive = toWitness {a? = 0ℚ ℚ.<? ⅛} tt

half quarter zero-branch : Dₚ Bool
half = choiceₚ ½ ½ (<⇒≤ half-positive) (<⇒≤ half-positive) refl (returnₚ true) (returnₚ false)
quarter = choiceₚ ¼ ¾ (<⇒≤ quarter-positive) (<⇒≤ three-quarter-positive) refl (returnₚ true) (returnₚ false)
zero-branch = choiceₚ 0ℚ 1ℚ ≤-refl 0≤1ℚ refl (returnₚ true) (returnₚ false)

half-support : ∀ b → Positive half b
half-support true = delay true _ half-positive refl (positive-return true)
half-support false = delay false _ half-positive refl (positive-return false)

quarter-support : ∀ b → Positive quarter b
quarter-support true = delay true _ quarter-positive refl (positive-return true)
quarter-support false = delay false _ three-quarter-positive refl (positive-return false)

full-support-to : {d e : Dₚ Bool} → (∀ b → Positive e b) → d ≼₊ e
full-support-to {d} support P nn (n , pos) =
  let b , path , value = positive-extract n d P nn pos
  in positive-witness P nn (support b) value

half≈quarter : half ≈₊ quarter
half≈quarter = full-support-to quarter-support , full-support-to half-support

quarter-cum : ∀ n → cum (suc (suc n)) quarter (indᵇ true) ≡ ¼
quarter-cum n = trans (cong₂ ℚ._+_
  (cong (¼ ℚ.*_) (returnₚ-cum n true (indᵇ true)))
  (cong (¾ ℚ.*_) (returnₚ-cum n false (indᵇ true)))) refl

half-cum : ∀ n → cum (suc (suc n)) half (indᵇ true) ≡ ½
half-cum n = trans (cong₂ ℚ._+_
  (cong (½ ℚ.*_) (returnₚ-cum n true (indᵇ true)))
  (cong (½ ℚ.*_) (returnₚ-cum n false (indᵇ true)))) refl

quarter-upper : ∀ n → cum n quarter (indᵇ true) ℚ.≤ ¼
quarter-upper zero = <⇒≤ quarter-positive
quarter-upper (suc zero) = ≤-trans (≤-reflexive (node-zero ¼ ¾)) (<⇒≤ quarter-positive)
quarter-upper (suc (suc n)) = ≤-reflexive (quarter-cum n)

half≉quarter : ¬ (half ≈ₚ quarter)
half≉quarter eq = toWitnessFalse {a? = ½ ℚ.≤? ¼} tt
  (subst (ℚ._≤ ¼) (half-cum 0) (≤-trans (proj₂ witness) (quarter-upper (proj₁ witness))))
  where witness = proj₁ eq (indᵇ true) (indᵇ-nn true) 2

half≁quarter : ¬ (∀ ε → 0ℚ ℚ.< ε → half ≈ₚ[ ε ] quarter)
half≁quarter eq = toWitnessFalse {a? = ½ ℚ.≤? (¼ ℚ.+ ⅛)} tt
  (subst (ℚ._≤ ¼ ℚ.+ ⅛) (half-cum 0)
    (≤-trans (proj₂ witness) (+-monoˡ-≤ ⅛ (quarter-upper (proj₁ witness)))))
  where witness = proj₁ (eq ⅛ eighth-positive) true 2

zero-erased : zero-branch ≈ₚ returnₚ false
zero-erased = shift⇒≈ₚ zero-branch (returnₚ false) λ P n →
  trans (cong₂ ℚ._+_ (*-zeroˡ (cum n (returnₚ true) P)) (*-identityˡ (cum n (returnₚ false) P)))
    (+-identityˡ (cum n (returnₚ false) P))

zero-excluded : ¬ PositiveTest zero-branch (indᵇ true)
zero-excluded pos with positive-test-cong (indᵇ-nn true) zero-erased pos
... | zero , p = <-irrefl refl p
... | suc n , p = <-irrefl (sym (returnₚ-cum n false (indᵇ true))) p

positive-distinguished : ¬ (zero-branch ≈₊ half)
positive-distinguished eq = zero-excluded (proj₂ eq (indᵇ true) (indᵇ-nn true)
  (positive-witness (indᵇ true) (indᵇ-nn true) (half-support true) 0<1ℚ))
