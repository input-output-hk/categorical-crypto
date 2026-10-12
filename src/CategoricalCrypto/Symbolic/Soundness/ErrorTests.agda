{-# OPTIONS --safe --without-K --guardedness #-}

-- A closed uniform-nonce experiment: a fixed finite program compares the
-- sampled nonce with at most N recorded guesses. Its one-system error is
-- N·2⁻η, but no negligible error can cover every finite N simultaneously.
-- This is not a Scheme/Backtranslation construction or a crypto reduction.
module CategoricalCrypto.Symbolic.Soundness.ErrorTests where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties using (length-++; length-map; length-take; take-all)
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Poly
open import Data.Product hiding (map)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; ½)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Properties.Ext
open import Data.Unit.Base
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation.Core

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Settle hiding (score)

open import CategoricalCrypto.Symbolic.Soundness.Errors
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Approximate.Decay
open import CategoricalCrypto.UC.Machine using (Approximationᴹ)

import CategoricalCrypto.UC.Approximate.Local as Local
import ProbabilisticLogic.Distribution.Uniform.Collision as Collision
import ProbabilisticLogic.Distribution.Uniform.Duplicate as Duplicate

private module Observation = Local Approximationᴹ ℕ (λ η → η)

allBits : (η : ℕ) → List (Vec Bool η)
allBits zero = Vec.[] ∷ []
allBits (suc η) = map (false Vec.∷_) (allBits η) ++ map (true Vec.∷_) (allBits η)

allBits-complete : ∀ {η} (h : Vec Bool η) → h ∈ allBits η
allBits-complete Vec.[] = here refl
allBits-complete (false Vec.∷ h) = ∈-++⁺ˡ (∈-map⁺ (false Vec.∷_) (allBits-complete h))
allBits-complete (true Vec.∷ h) = ∈-++⁺ʳ _ (∈-map⁺ (true Vec.∷_) (allBits-complete h))

allBits-length : (η : ℕ) → length (allBits η) ≡ 2 ^ η
allBits-length zero = refl
allBits-length (suc η) = trans
  (length-++ (map (false Vec.∷_) (allBits η)) {ys = map (true Vec.∷_) (allBits η)})
  (trans (cong₂ _+_ (trans (length-map (false Vec.∷_) (allBits η)) (allBits-length η))
                    (trans (length-map (true Vec.∷_) (allBits η)) (allBits-length η)))
         (sym (cong (2 ^ η +_) (ℕₚ.+-identityʳ (2 ^ η)))))

guesses : (N η : ℕ) → List (Vec Bool η)
guesses N η = take N (allBits η)

guesses-bounded : (N η : ℕ) → length (guesses N η) ℕ.≤ N
guesses-bounded N η = subst (ℕ._≤ N) (sym (length-take N (allBits η)))
  (ℕₚ.m⊓n≤m N (length (allBits η)))

private
  ∈-memb : ∀ {η} {h : Vec Bool η} (hs : List (Vec Bool η))
    → h ∈ hs → Duplicate.memb η h hs ≡ true
  ∈-memb {η} {h} hs p with Duplicate.memb η h hs in e
  ... | true = refl
  ... | false = ⊥-elim (Duplicate.memb-∉ η hs h e p)

observe : (N η : ℕ) → Dₚ Bool
observe N η = mapₚ (λ h → Duplicate.memb η h (guesses N η)) (uniformₚ η)

predicted : (N η : ℕ) → Dₚ Bool
predicted _ _ = returnₚ false

error : (N η : ℕ) → ℚ
error N η = fromℕ N ℚ.* inv-pow-2 η

private
  distribution : (N η : ℕ) → Dist-ℚ Bool
  distribution N η = uniform-Vec η >>=ᴹ λ h → return-ℚ (Duplicate.memb η h (guesses N η))

  observation-settles : (N η : ℕ) → Σ[ n ∈ ℕ ] Settlesᵀ n (observe N η) (distribution N η)
  observation-settles N η = Settlesᵀ-bind⋆ _ (uniformₚ η)
    (λ h → returnₚ (Duplicate.memb η h (guesses N η))) (uniform-Vec η)
    (λ h → return-ℚ (Duplicate.memb η h (guesses N η))) (proj₂ (uniformₚ-settles η))
    (λ h → 1 , Settlesᵀ-return (Duplicate.memb η h (guesses N η)))

  score : (N η : ℕ) (P : Bool → ℚ) → E (distribution N η) P
    ≡ E (uniform-Vec η) (λ h → P (Duplicate.memb η h (guesses N η)))
  score N η P = trans (E-bind (uniform-Vec η)
    (λ h → return-ℚ (Duplicate.memb η h (guesses N η))) P)
    (lookupᴰℚ-cong-P (entries (uniform-Vec η)) λ h →
      lookupᴰℚ-return (Duplicate.memb η h (guesses N η)) P)

  true-bound : (N η : ℕ) → Pr₁ (distribution N η) ℚ.≤ error N η
  true-bound N η = ℚₚ.≤-trans (ℚₚ.≤-reflexive (score N η bool→ℚ))
    (ℚₚ.≤-trans (E-mono (uniform-Vec η) _ _ (Duplicate.indicator-≤ η (guesses N η)))
    (ℚₚ.≤-trans (ℚₚ.≤-reflexive (Collision.E-countMatch η (guesses N η)))
      (ℚₚ.*-monoʳ-≤-nonNeg (inv-pow-2 η) ⦃ ℚ.nonNegative (0≤inv-pow-2 η) ⦄
        (fromℕ-mono-≤ (guesses-bounded N η)))))

  cap : ∀ {n N η} → Settlesᵀ n (observe N η) (distribution N η)
    → (b : Bool) (k : ℕ) → Pr≤[ b ] k (observe N η) ℚ.≤ E (distribution N η) (indᵇ b)
  cap {n} {N} {η} s b k = ℚₚ.≤-trans
    (cum-mono (ℕₚ.m≤n+m k n) (observe N η) (indᵇ b) (indᵇ-nn b))
    (ℚₚ.≤-reflexive (Settlesᵀ-cum s (indᵇ-nn b) (n + k) (ℕₚ.m≤m+n n k)))

  one-system : (N η : ℕ) → observe N η ≈ₚ[ error N η ] predicted N η
  one-system N η = below , above
    where
    n = proj₁ (observation-settles N η)
    s = proj₂ (observation-settles N η)
    ε≥0 = 0≤* (0≤fromℕ N) (0≤inv-pow-2 η)

    lower-false : 1ℚ ℚ.≤ E (distribution N η) (indᵇ false) ℚ.+ error N η
    lower-false = ℚₚ.≤-trans (ℚₚ.≤-reflexive (sym (−-+-cancel 1ℚ (Pr₁ (distribution N η)))))
      (ℚₚ.≤-trans (ℚₚ.+-monoʳ-≤ (1ℚ ℚ.- Pr₁ (distribution N η)) (true-bound N η))
        (ℚₚ.≤-reflexive (cong (ℚ._+ error N η) (sym (E-not (distribution N η))))))

    below : observe N η ≼ₚ[ error N η ] predicted N η
    below true k = 1 , ℚₚ.≤-trans (cap {N = N} {η} s true k)
      (ℚₚ.≤-trans (true-bound N η)
        (ℚₚ.≤-reflexive (sym (trans (cong (ℚ._+ error N η) (returnₚ-cum 0 false bool→ℚ))
          (ℚₚ.+-identityˡ (error N η))))))
    below false k = 1 , ℚₚ.≤-trans (cap {N = N} {η} s false k)
      (ℚₚ.≤-trans (ℚₚ.≤-trans (E-mono (distribution N η) _ _ (indᵇ-≤1 false))
        (ℚₚ.≤-reflexive (E-const (distribution N η) 1ℚ))) (p≤p+q 1ℚ ε≥0))

    above : predicted N η ≼ₚ[ error N η ] observe N η
    above true k = n , ℚₚ.≤-trans (returnₚ-cum-≤ k false bool→ℚ 0≤bool)
      (ℚₚ.≤-trans ε≥0 (p≤q+p (error N η) (cum-nn n (observe N η) bool→ℚ 0≤bool)))
    above false k = n , ℚₚ.≤-trans (returnₚ-cum-≤ k false (indᵇ false) (indᵇ-nn false))
      (subst (λ x → 1ℚ ℚ.≤ x ℚ.+ error N η)
        (sym (Settlesᵀ-cum s (indᵇ-nn false) n ℕₚ.≤-refl)) lower-false)

nonce-approximation : ProtocolError ℕ (λ _ → ⊤) observe predicted
nonce-approximation = record
  { error = error
  ; negligible-error = λ N _ → negligible-inv-pow-2 (poly-const N) (λ _ → ℕₚ.≤-refl)
  ; realizes = λ N _ → one-system N }

comparison-at : (N M η : ℕ) → observe N η ≈ₚ[ error N η ℚ.+ error M η ] observe M η
comparison-at N M = Comparison.compare-at nonce-approximation N M tt tt (λ _ → ≈ₚ-refl _)

comparison : (N M : ℕ) → observe N Observation.∼ᴺ observe M
comparison N M = Comparison.compare nonce-approximation N M tt tt (λ _ → ≈ₚ-refl _)

private
  exhaustive-score : (η : ℕ) → Pr₁ (distribution (2 ^ η) η) ≡ 1ℚ
  exhaustive-score η = trans (score (2 ^ η) η bool→ℚ)
    (trans (lookupᴰℚ-cong-P (entries (uniform-Vec η)) λ h → cong bool→ℚ
      (∈-memb (guesses (2 ^ η) η)
        (subst (h ∈_) (sym (take-all (2 ^ η) (allBits η) (ℕₚ.≤-reflexive (allBits-length η))))
          (allBits-complete h)))) (E-const (uniform-Vec η) 1ℚ))

  zero-score : (η : ℕ) → Pr₁ (distribution 0 η) ≡ 0ℚ
  zero-score η = trans (score 0 η bool→ℚ) (E-const (uniform-Vec η) 0ℚ)

no-uniform-comparison : (ε : ℕ → ℚ) → Negligible ε
  → ¬ ((N η : ℕ) → observe N η ≈ₚ[ ε η ] observe 0 η)
no-uniform-comparison ε neg uniform = 1≰½ (ℚₚ.≤-trans (floor N) (small N ℕₚ.≤-refl))
  where
  floor : (η : ℕ) → 1ℚ ℚ.≤ ε η
  floor η = let n , s = observation-settles (2 ^ η) η
                k , bd = proj₁ (uniform (2 ^ η) η) true n
                t = proj₂ (observation-settles 0 η)
    in ℚₚ.≤-trans (ℚₚ.≤-reflexive (sym (trans (Settlesᵀ-cum s 0≤bool n ℕₚ.≤-refl) (exhaustive-score η))))
      (ℚₚ.≤-trans bd (ℚₚ.≤-trans (ℚₚ.+-monoˡ-≤ (ε η) (cap {N = 0} {η} t true k))
        (ℚₚ.≤-reflexive (trans (cong (ℚ._+ ε η) (zero-score η)) (ℚₚ.+-identityˡ (ε η))))))

  N = proj₁ (Negligible⇒→0 neg ½ (ℚₚ.positive⁻¹ ½))
  small = proj₂ (Negligible⇒→0 neg ½ (ℚₚ.positive⁻¹ ½))

-- Shared prediction can be any subdistribution; it need not be `false`.
-- This is the old uniform-error factorization shape after classification has
-- made the predicted observations equal for the tested protocols.
no-uniform-factorization : (shared : ℕ → Dₚ Bool) (ε : ℕ → ℚ) → Negligible ε
  → ¬ ((N η : ℕ) → observe N η ≈ₚ[ ε η ] shared η)
no-uniform-factorization shared ε neg realizes = no-uniform-comparison
  (λ η → ε η ℚ.+ ε η) (Negligible-+ neg neg)
  (λ N η → ≈ₚ[]-trans (realizes N η) (≈ₚ[]-sym (realizes 0 η)))
