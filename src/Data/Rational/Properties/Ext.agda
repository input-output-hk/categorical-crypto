{-# OPTIONS --safe --without-K #-}

-- The ℚ rearrangements `Data.Rational.Properties` does not export: the additive
-- group facts (via `Algebra.Properties.AbelianGroup` at `+-0-abelianGroup`) and
-- the absolute-value bounds the distinguishing-advantage arithmetic runs on.

module Data.Rational.Properties.Ext where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; ∣_∣; _≤_; nonNegative)
open import Data.Rational.Properties using
  ( +-0-abelianGroup; +-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ
  ; +-monoʳ-≤; ≤-reflexive; ≤-total; ≤-trans; neg-antimono-≤
  ; 0≤p⇒∣p∣≡p; 0≤∣p∣; ∣-p∣≡∣p∣; nonNegative⁻¹; nonNeg*nonNeg⇒nonNeg )
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; subst)

import Algebra.Properties.AbelianGroup as AbelianGroupProperties

private module AG = AbelianGroupProperties +-0-abelianGroup

private variable x y c : ℚ

neg-sub : ∀ p q → p - q ≡ - (q - p)
neg-sub p q = sym (AG.⁻¹-anti-homo‿- q p)

+-−-cancel : ∀ x d → (x + d) - d ≡ x
+-−-cancel x d = trans (+-assoc x d (- d)) (trans (cong (x +_) (+-inverseʳ d)) (+-identityʳ x))

−-+-cancel : ∀ x d → (x - d) + d ≡ x
−-+-cancel x d = trans (+-assoc x (- d) d) (trans (cong (x +_) (+-inverseˡ d)) (+-identityʳ x))

telescope : ∀ a b c → (a - b) + (b - c) ≡ a - c
telescope a b c = trans (+-assoc a (- b) (b - c))
  (cong (a +_) (trans (sym (+-assoc (- b) b (- c)))
                  (trans (cong (_+ (- c)) (+-inverseˡ b)) (+-identityˡ (- c)))))

0≤1ℚ : 0ℚ ≤ 1ℚ
0≤1ℚ = 0≤∣p∣ 1ℚ

-- The `_≤_` spelling of `nonNeg*nonNeg⇒nonNeg`, which is stated in the
-- instance-argument `NonNegative` idiom.
0≤* : 0ℚ ≤ x → 0ℚ ≤ y → 0ℚ ≤ x * y
0≤* {x} {y} 0≤x 0≤y = nonNegative⁻¹ (x * y)
  {{nonNeg*nonNeg⇒nonNeg x {{nonNegative 0≤x}} y {{nonNegative 0≤y}}}}

neg≤0 : 0ℚ ≤ y → (- y) ≤ 0ℚ
neg≤0 = neg-antimono-≤

x-y≤x : ∀ x → 0ℚ ≤ y → (x - y) ≤ x
x-y≤x x 0≤y = ≤-trans (+-monoʳ-≤ x (neg≤0 0≤y)) (≤-reflexive (+-identityʳ x))

p≤∣p∣ : ∀ p → p ≤ ∣ p ∣
p≤∣p∣ p with ≤-total 0ℚ p
... | inj₁ 0≤p = ≤-reflexive (sym (0≤p⇒∣p∣≡p 0≤p))
... | inj₂ p≤0 = ≤-trans p≤0 (0≤∣p∣ p)

-- ∣x∣ ≤ c  from  x ≤ c  and  -x ≤ c
∣∣≤ : x ≤ c → (- x) ≤ c → ∣ x ∣ ≤ c
∣∣≤ {x} {c} x≤c -x≤c with ≤-total 0ℚ x
... | inj₁ 0≤x = subst (_≤ c) (sym (0≤p⇒∣p∣≡p 0≤x)) x≤c
... | inj₂ x≤0 = subst (_≤ c) (sym ∣x∣≡-x) -x≤c
  where ∣x∣≡-x = trans (sym (∣-p∣≡∣p∣ x)) (0≤p⇒∣p∣≡p (neg-antimono-≤ x≤0))

∣diff∣≤1 : 0ℚ ≤ x → x ≤ 1ℚ → 0ℚ ≤ y → y ≤ 1ℚ → ∣ x - y ∣ ≤ 1ℚ
∣diff∣≤1 {x} {y} 0≤x x≤1 0≤y y≤1 =
  ∣∣≤ (≤-trans (x-y≤x x 0≤y) x≤1)
      (subst (_≤ 1ℚ) (neg-sub y x) (≤-trans (x-y≤x y 0≤x) y≤1))
