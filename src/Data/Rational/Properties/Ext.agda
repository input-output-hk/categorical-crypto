{-# OPTIONS --safe --without-K #-}

-- The ℚ rearrangements `Data.Rational.Properties` does not export: the additive
-- group facts (via `Algebra.Properties.AbelianGroup` at `+-0-abelianGroup`), the
-- absolute-value bounds the distinguishing-advantage arithmetic runs on, and the
-- arithmetic of the `_/_` constructor.

module Data.Rational.Properties.Ext where

open import Data.Integer as ℤ using (ℤ)
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; ½; _+_; _-_; -_; _*_; _/_; ∣_∣; _≤_; _<_; nonNegative; toℚᵘ)
open import Data.Rational.Properties using
  ( +-0-abelianGroup; +-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ
  ; +-monoʳ-≤; ≤-reflexive; ≤-total; ≤-trans; neg-antimono-≤
  ; 0≤p⇒∣p∣≡p; 0≤∣p∣; ∣-p∣≡∣p∣; nonNegative⁻¹; nonNeg*nonNeg⇒nonNeg
  ; *-distribʳ-+; *-identityˡ; *-monoʳ-<-pos; *-zeroʳ
  ; toℚᵘ-cancel-≤; toℚᵘ-fromℚᵘ; toℚᵘ-homo-*; toℚᵘ-homo-+; toℚᵘ-injective )
open import Data.Rational.Unnormalised.Base as ℚᵘ using (mkℚᵘ; *≤*)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import Algebra.Properties.AbelianGroup as AbelianGroupProperties
import Data.Rational.Unnormalised.Properties as ℚᵘₚ

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

------------------------------------------------------------------------
-- Halving, for ε/2 + ε/2 arguments

0<½* : 0ℚ < x → 0ℚ < ½ * x
0<½* {x} 0<x = subst (_< ½ * x) (*-zeroʳ ½) (*-monoʳ-<-pos ½ 0<x)

½*+½* : ∀ x → ½ * x + ½ * x ≡ x
½*+½* x = trans (sym (*-distribʳ-+ x ½ ½)) (*-identityˡ x)

------------------------------------------------------------------------
-- Arithmetic and order for the `_/_` constructor
------------------------------------------------------------------------

-- All three go through ℚᵘ, where `_/_` IS the constructor and `_≤_`, `_+_`,
-- `_*_` are the naive numerator/denominator formulas (no normalization).

private
  toℚᵘ-/ : ∀ (i : ℤ) (n : ℕ) .{{_ : ℕ.NonZero n}} → toℚᵘ (i / n) ℚᵘ.≃ i ℚᵘ./ n
  toℚᵘ-/ i (suc n) = toℚᵘ-fromℚᵘ (mkℚᵘ i n)

/-mono-≤ : ∀ (i : ℤ) (n : ℕ) (j : ℤ) (m : ℕ) .{{_ : ℕ.NonZero n}} .{{_ : ℕ.NonZero m}}
         → i ℤ.* (ℤ.+ m) ℤ.≤ j ℤ.* (ℤ.+ n) → i / n ≤ j / m
/-mono-≤ i n@(suc _) j m@(suc _) le = toℚᵘ-cancel-≤
  (ℚᵘₚ.≤-respˡ-≃ (ℚᵘₚ.≃-sym (toℚᵘ-/ i n))
    (ℚᵘₚ.≤-respʳ-≃ (ℚᵘₚ.≃-sym (toℚᵘ-/ j m)) (*≤* le)))

-- The two-fraction laws quantify over `suc n` rather than a `NonZero n`, so
-- that the product denominator's own `NonZero` is found by reduction.
/-*-/ : ∀ (i : ℤ) (n : ℕ) (j : ℤ) (m : ℕ)
      → (i / suc n) * (j / suc m) ≡ (i ℤ.* j) / (suc n ℕ.* suc m)
/-*-/ i n j m = toℚᵘ-injective
  (ℚᵘₚ.≃-trans (toℚᵘ-homo-* (i / suc n) (j / suc m))
    (ℚᵘₚ.≃-trans (ℚᵘₚ.*-cong (toℚᵘ-/ i (suc n)) (toℚᵘ-/ j (suc m)))
                 (ℚᵘₚ.≃-sym (toℚᵘ-/ (i ℤ.* j) (suc n ℕ.* suc m)))))

/-+-/ : ∀ (i : ℤ) (n : ℕ) (j : ℤ) (m : ℕ)
      → (i / suc n) + (j / suc m)
        ≡ (i ℤ.* (ℤ.+ suc m) ℤ.+ j ℤ.* (ℤ.+ suc n)) / (suc n ℕ.* suc m)
/-+-/ i n j m = toℚᵘ-injective
  (ℚᵘₚ.≃-trans (toℚᵘ-homo-+ (i / suc n) (j / suc m))
    (ℚᵘₚ.≃-trans (ℚᵘₚ.+-cong (toℚᵘ-/ i (suc n)) (toℚᵘ-/ j (suc m)))
                 (ℚᵘₚ.≃-sym (toℚᵘ-/ (i ℤ.* (ℤ.+ suc m) ℤ.+ j ℤ.* (ℤ.+ suc n))
                                    (suc n ℕ.* suc m)))))
