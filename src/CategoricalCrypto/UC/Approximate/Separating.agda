{-# OPTIONS --safe --without-K #-}

-- The two instruments a NEGATIVE statement about closeness needs.
--
-- An `Approximation` is an interface, and a rejection is not provable against
-- it: the relation that identifies everything at every error satisfies all four
-- laws, so `x ≈[ ε ] y` alone never bounds a gap from below.  `ℚ-metric` is the
-- faithful instance — closeness IS the distance — and it is what turns a
-- statement of the form "this difference is not admitted" into a theorem.
--
-- The second instrument is a sequence the `Negligible` grade excludes.
-- `1/(n+1)` is the canonical one, and it is exactly the gap between the two
-- grades: it vanishes (`UC.Approximate._→0`, whose header names it) and no
-- polynomial magnification of it does, since `n+1` cancels it outright.
-- `Decay` is the positive counterpart, at the exponential schedule.

open import Data.Integer.Base using (+_; +<+)
open import Data.Nat.Base as ℕ using (ℕ; suc; z≤n; s≤s)
open import Data.Nat.Poly using (poly-+; poly-const; poly-id)
open import Data.Nat.Properties as ℕₚ using ()
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; ½; ∣_∣; 1/_; NonZero; positive; *<*)
open import Data.Rational.Properties
  using ( *-inverseʳ; +-inverseʳ; +-identityʳ; +-mono-≤; <-irrefl; ≤-<-trans; ≤-refl
        ; ≤-reflexive; ≤-trans; 0≤p⇒∣p∣≡p; ∣-p∣≡∣p∣; ∣p+q∣≤∣p∣+∣q∣
        ; pos⇒nonZero; positive⁻¹ )
open import Data.Rational.Properties.Ext using (neg-sub; p≤∣p∣; telescope)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; subst; sym; trans)
open import Relation.Nullary using (¬_)

open import ProbabilisticLogic.Distribution.Uniform using (fromℕ; fromℕ-/; 0<fromℕ-suc)

open import CategoricalCrypto.UC.Approximate using (Approximation; Negligible; ℚ-errors)

module CategoricalCrypto.UC.Approximate.Separating where

------------------------------------------------------------------------
-- ℚ at its own metric

infix 4 _≈ᵐ[_]_

_≈ᵐ[_]_ : ℚ → ℚ → ℚ → Set
x ≈ᵐ[ ε ] y = ∣ x ℚ.- y ∣ ℚ.≤ ε

ℚ-metric : Approximation ℚ ℚ-errors 0ℓ
ℚ-metric = record
  { _≈[_]_    = _≈ᵐ[_]_
  ; ≈[]-refl  = λ {x} → ≤-reflexive (trans (cong ∣_∣ (+-inverseʳ x)) (0≤p⇒∣p∣≡p ≤-refl))
  ; ≈[]-sym   = λ {x} {y} →
      subst (ℚ._≤ _) (sym (trans (cong ∣_∣ (neg-sub y x)) (∣-p∣≡∣p∣ (x ℚ.- y))))
  ; ≈[]-trans = λ {x} {y} {z} h k → ≤-trans
      (≤-trans (≤-reflexive (cong ∣_∣ (sym (telescope x y z))))
               (∣p+q∣≤∣p∣+∣q∣ (x ℚ.- y) (y ℚ.- z)))
      (+-mono-≤ h k)
  ; ≈[]-mono  = λ le h → ≤-trans h le
  }

-- Closeness to zero at exactly the value, and the gap back out: the metric
-- neither inflates a difference nor hides one.  The second is the half no
-- abstract approximation can supply.
≈ᵐ-0 : {x : ℚ} → 0ℚ ℚ.≤ x → x ≈ᵐ[ x ] 0ℚ
≈ᵐ-0 {x} 0≤x = ≤-reflexive (trans (cong ∣_∣ (+-identityʳ x)) (0≤p⇒∣p∣≡p 0≤x))

≈ᵐ-gap : {x ε : ℚ} → x ≈ᵐ[ ε ] 0ℚ → x ℚ.≤ ε
≈ᵐ-gap {x} h = ≤-trans (≤-trans (p≤∣p∣ x) (≤-reflexive (cong ∣_∣ (sym (+-identityʳ x))))) h

------------------------------------------------------------------------
-- The inverse-polynomial floor

-- The witness is passed EXPLICITLY: `NonZero` unfolds to a predicate on the
-- numerator, so instance search cannot read `n` back out of the goal.
private
  nzᶠ : (n : ℕ) → NonZero (fromℕ (suc n))
  nzᶠ n = pos⇒nonZero (fromℕ (suc n)) {{positive (0<fromℕ-suc n)}}

inv-suc : ℕ → ℚ
inv-suc n = 1/_ (fromℕ (suc n)) {{nzᶠ n}}

-- The magnifier `n+1` turns it into the constant `1`, which does not vanish.
-- `½ < 1` is the cross-multiplication `1 · 1 < 1 · 2`.
¬negligible-inv-suc : ¬ Negligible inv-suc
¬negligible-inv-suc neg =
  let N , bnd = neg (λ n → 1 ℕ.+ n) (poly-+ (poly-const 1) poly-id) ½ (positive⁻¹ ½)
      1≤½ = subst (ℚ._≤ ½)
              (trans (cong (ℚ._* inv-suc N) (sym (fromℕ-/ (suc N))))
                     (*-inverseʳ (fromℕ (suc N)) {{nzᶠ N}}))
              (bnd N ℕₚ.≤-refl)
  in <-irrefl refl (≤-<-trans 1≤½ (*<* (+<+ (s≤s (s≤s z≤n)))))
