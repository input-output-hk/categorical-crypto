{-# OPTIONS --safe --without-K #-}

-- The ℚ rearrangements `Data.Rational.Properties` does not export: the additive
-- group facts (via `Algebra.Properties.AbelianGroup` at `+-0-abelianGroup`), the
-- absolute-value bounds the distinguishing-advantage arithmetic runs on, the two
-- order refutations at literals that a vanishing bound needs against probability
-- one, and the arithmetic of the `_/_` constructor.

module Data.Rational.Properties.Ext where

open import Data.Integer as ℤ using (ℤ)
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; ½; _+_; _-_; -_; _*_; _/_; ∣_∣; _≤_; _≤?_; _<_; nonNegative; toℚᵘ)
open import Data.Rational.Properties using
  ( +-0-abelianGroup; +-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ
  ; +-monoʳ-≤; ≤-refl; ≤-reflexive; ≤-total; ≤-trans; neg-antimono-≤
  ; 0≤p⇒∣p∣≡p; 0≤∣p∣; ∣-p∣≡∣p∣; ∣p+q∣≤∣p∣+∣q∣; nonNegative⁻¹; nonNeg*nonNeg⇒nonNeg
  ; *-distribʳ-+; *-identityˡ; *-monoʳ-<-pos; *-zeroʳ
  ; toℚᵘ-cancel-≤; toℚᵘ-fromℚᵘ; toℚᵘ-homo-*; toℚᵘ-homo-+; toℚᵘ-injective )
open import Data.Rational.Unnormalised.Base as ℚᵘ using (mkℚᵘ; *≡*; *≤*)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable.Core using (toWitnessFalse)
open import Relation.Nullary.Negation.Core using (¬_)

import Algebra.Properties.AbelianGroup as AbelianGroupProperties
import Data.Integer.Properties as ℤₚ
import Data.Rational.Unnormalised.Properties as ℚᵘₚ

private module AG = AbelianGroupProperties +-0-abelianGroup

private variable x y c : ℚ

0≤1ℚ : 0ℚ ≤ 1ℚ
0≤1ℚ = 0≤∣p∣ 1ℚ

-- The `_≤_` spelling of `nonNeg*nonNeg⇒nonNeg`, which is stated in the
-- instance-argument `NonNegative` idiom.
0≤* : 0ℚ ≤ x → 0ℚ ≤ y → 0ℚ ≤ x * y
0≤* {x} {y} 0≤x 0≤y = nonNegative⁻¹ (x * y)
  {{nonNeg*nonNeg⇒nonNeg x {{nonNegative 0≤x}} y {{nonNegative 0≤y}}}}

------------------------------------------------------------------------
-- Halving, for ε/2 + ε/2 arguments

0<½* : 0ℚ < x → 0ℚ < ½ * x
0<½* {x} 0<x = subst (_< ½ * x) (*-zeroʳ ½) (*-monoʳ-<-pos ½ 0<x)

½*+½* : ∀ x → ½ * x + ½ * x ≡ x
½*+½* x = trans (sym (*-distribʳ-+ x ½ ½)) (*-identityˡ x)

------------------------------------------------------------------------
-- Arithmetic and order for the `_/_` constructor
------------------------------------------------------------------------

-- All four go through ℚᵘ, where `_/_` IS the constructor and `_≤_`, `_+_`,
-- `_*_` are the naive numerator/denominator formulas (no normalization).

private
  toℚᵘ-/ : ∀ (i : ℤ) (n : ℕ) .{{_ : ℕ.NonZero n}} → toℚᵘ (i / n) ℚᵘ.≃ i ℚᵘ./ n
  toℚᵘ-/ i (suc n) = toℚᵘ-fromℚᵘ (mkℚᵘ i n)

/-mono-≤ : ∀ (i : ℤ) (n : ℕ) (j : ℤ) (m : ℕ) .{{_ : ℕ.NonZero n}} .{{_ : ℕ.NonZero m}}
         → i ℤ.* (ℤ.+ m) ℤ.≤ j ℤ.* (ℤ.+ n) → i / n ≤ j / m
/-mono-≤ i n@(suc _) j m@(suc _) le = toℚᵘ-cancel-≤
  (ℚᵘₚ.≤-respˡ-≃ (ℚᵘₚ.≃-sym (toℚᵘ-/ i n))
    (ℚᵘₚ.≤-respʳ-≃ (ℚᵘₚ.≃-sym (toℚᵘ-/ j m)) (*≤* le)))

/-*-/ : ∀ (i : ℤ) (n : ℕ) (j : ℤ) (m : ℕ)
        .{{_ : ℕ.NonZero n}} .{{_ : ℕ.NonZero m}} .{{_ : ℕ.NonZero (n ℕ.* m)}}
      → (i / n) * (j / m) ≡ (i ℤ.* j) / (n ℕ.* m)
/-*-/ i n@(suc _) j m@(suc _) = toℚᵘ-injective
  (ℚᵘₚ.≃-trans (toℚᵘ-homo-* (i / n) (j / m))
    (ℚᵘₚ.≃-trans (ℚᵘₚ.*-cong (toℚᵘ-/ i n) (toℚᵘ-/ j m))
                 (ℚᵘₚ.≃-sym (toℚᵘ-/ (i ℤ.* j) (n ℕ.* m)))))

/-+-/ : ∀ (i : ℤ) (n : ℕ) (j : ℤ) (m : ℕ)
        .{{_ : ℕ.NonZero n}} .{{_ : ℕ.NonZero m}} .{{_ : ℕ.NonZero (n ℕ.* m)}}
      → (i / n) + (j / m)
        ≡ (i ℤ.* (ℤ.+ m) ℤ.+ j ℤ.* (ℤ.+ n)) / (n ℕ.* m)
/-+-/ i n@(suc _) j m@(suc _) = toℚᵘ-injective
  (ℚᵘₚ.≃-trans (toℚᵘ-homo-+ (i / n) (j / m))
    (ℚᵘₚ.≃-trans (ℚᵘₚ.+-cong (toℚᵘ-/ i n) (toℚᵘ-/ j m))
                 (ℚᵘₚ.≃-sym (toℚᵘ-/ (i ℤ.* (ℤ.+ m) ℤ.+ j ℤ.* (ℤ.+ n)) (n ℕ.* m)))))
