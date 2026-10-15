{-# OPTIONS --safe --without-K --guardedness #-}

-- Literal positive paths and rationally observable positive events differ on
-- arbitrary carriers: reflecting the former through ≈ₚ implies stable equality.

module ProbabilisticLogic.Dp.Positive where

open import Data.Bool.Base
open import Data.Empty
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Data.Sum.Base
open import Data.Sum.Properties using (inj₁-injective)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable.Core using (yes; no)

open import ProbabilisticLogic.Dp

private variable
  a : Level
  A : Set a

-- Every traversed branch, including the final branch, has positive weight.
data Positive {A : Set a} (d : Dₚ A) (x : A) : Set a where
  hit : (c : Bool) → 0ℚ ℚ.< wt d c → br d c ≡ inj₁ x → Positive d x
  delay : (c : Bool) (e : Dₚ A) → 0ℚ ℚ.< wt d c → br d c ≡ inj₂ e
        → Positive e x → Positive d x

positive-return : (x : A) → Positive (returnₚ x) x
positive-return x = hit true 0<1ℚ refl

positive-return-reflect : {x y : A} → Positive (returnₚ x) y → x ≡ y
positive-return-reflect (hit c p eq) = inj₁-injective eq
positive-return-reflect (delay c e p () q)

rational-separation : {x y : A} → ¬ ¬ (x ≡ y) → (P : A → ℚ) → P x ≡ P y
rational-separation {x = x} {y} nn P with P x ≟ P y
... | yes eq = eq
... | no neq = ⊥-elim (nn (λ eq → neq (cong P eq)))

return-double-negation : {x y : A} → ¬ ¬ (x ≡ y) → returnₚ x ≈ₚ returnₚ y
return-double-negation {x = x} {y} nn = exact⇒≈ₚ (returnₚ x) (returnₚ y) λ where
  P zero → refl
  P (suc n) → trans (returnₚ-cum n x P)
    (trans (rational-separation nn P) (sym (returnₚ-cum n y P)))

LiteralSupportCongruence : (a : Level) → Set (Level.suc a)
LiteralSupportCongruence a = ∀ {A : Set a} {d e : Dₚ A} {x : A}
                          → d ≈ₚ e → Positive d x → Positive e x

literal-support-congruence⇒stable-equality : LiteralSupportCongruence a
  → {A : Set a} {x y : A} → ¬ ¬ (x ≡ y) → x ≡ y
literal-support-congruence⇒stable-equality stable {x = x} {y} nn =
  sym (positive-return-reflect (stable (return-double-negation nn) (positive-return x)))

PositiveTest : Dₚ A → (A → ℚ) → Set _
PositiveTest d P = Σ[ n ∈ ℕ ] 0ℚ ℚ.< cum n d P

positive-test-to : {d e : Dₚ A} {P : A → ℚ} → NNF P → d ≼ₚ e
                 → PositiveTest d P → PositiveTest e P
positive-test-to {P = P} nn de (n , pos) =
  let m , bound = de P nn n
  in m , <-≤-trans pos bound

positive-test-cong : {d e : Dₚ A} {P : A → ℚ} → NNF P → d ≈ₚ e
                   → PositiveTest d P → PositiveTest e P
positive-test-cong nn eq = positive-test-to nn (proj₁ eq)
