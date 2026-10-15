{-# OPTIONS --safe --without-K #-}

-- Exact finite rational sampling; zero-weight suffixes need no division.
module CategoricalCrypto.SSP.Dist.Sampling where

open import Algebra using (CommutativeRing)
open import Data.Bool.Base using (Bool; false; true)
open import Data.List.Base using (List; []; _∷_)
import Data.List.NonEmpty as NE
import Data.List.Relation.Unary.All as All
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext using (0≤*; nonNeg+nonNeg≡0)
open import Data.Rational.Solver
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (yes; no)

open import CategoricalCrypto.SSP.Dist.Kernel using (Coins; done; toss; sample)
import ProbabilisticLogic.Distribution.Linearity as Linearity
open import ProbabilisticLogic.Distribution.RationalDist

private variable A : Set

private
  module Lin = Linearity (CommutativeRing.commutativeSemiring +-*-commutativeRing)
  weighted : List (ℚ × A) → (A → ℚ) → ℚ
  weighted = Lin.lookup-L

  mass-nn : (xs : List (ℚ × A)) → NonNeg-L xs → 0ℚ ≤ mass-L xs
  mass-nn [] All.[] = ≤-refl
  mass-nn ((q , x) ∷ xs) (n All.∷ ns) = +-mono-≤ n (mass-nn xs ns)

  zero-weighted : (xs : List (ℚ × A)) → NonNeg-L xs → mass-L xs ≡ 0ℚ
    → (P : A → ℚ) → weighted xs P ≡ 0ℚ
  zero-weighted [] All.[] z P = refl
  zero-weighted ((q , x) ∷ xs) (n All.∷ ns) z P =
    let q0 , xs0 = nonNeg+nonNeg≡0 q (mass-L xs) n (mass-nn xs ns) z
    in trans (cong₂ _+_ (trans (cong (_* P x) q0) (*-zeroˡ (P x)))
      (zero-weighted xs ns xs0 P)) (+-identityˡ 0ℚ)

  inverse-nn : (m : ℚ) → 0ℚ ≤ m → (nz : m ≢ 0ℚ)
    → 0ℚ ≤ (1/ m) {{≢-nonZero nz}}
  inverse-nn m n nz = nonNegative⁻¹ i {{pos⇒nonNeg i
    {{1/pos⇒pos m {{nonNeg∧nonZero⇒pos m {{nonNegative n}} {{≢-nonZero nz}}}}}}}}
    where i = (1/ m) {{≢-nonZero nz}}

  split : (q r : ℚ) → 0ℚ ≤ q → 0ℚ ≤ r → (nz : q + r ≢ 0ℚ) → Dist-ℚ Bool
  split q r nq nr nz = mk-Dist
    ((q * i , false) NE.∷ (r * i , true) ∷ [])
    (trans (cong (q * i +_) (+-identityʳ (r * i)))
      (trans (sym (*-distribʳ-+ i q r)) (*-inverseʳ (q + r) {{≢-nonZero nz}})))
    (0≤* nq ni All.∷ 0≤* nr ni All.∷ All.[])
    where
    i = (1/ (q + r)) {{≢-nonZero nz}}
    ni = inverse-nn (q + r) (+-mono-≤ nq nr) nz

  chooseList : (fallback : A) (xs : List (ℚ × A)) → NonNeg-L xs → Coins A
  chooseList fallback [] All.[] = done fallback
  chooseList fallback ((q , x) ∷ []) (n All.∷ All.[]) = done x
  chooseList fallback ((q , x) ∷ xs@(e ∷ rest)) (n All.∷ ns) with (q + mass-L xs) ≟ 0ℚ
  ... | yes z = done fallback
  ... | no nz = toss (split q (mass-L xs) n (mass-nn xs ns) nz) λ where
      false → done x
      true → chooseList fallback xs ns

  cancel-scale : (m q r u v : ℚ) (nz : m ≢ 0ℚ)
    → m * (q * (1/ m) {{≢-nonZero nz}} * u + r * (1/ m) {{≢-nonZero nz}} * v)
      ≡ q * u + r * v
  cancel-scale m q r u v nz = trans (rearrange m q r u v _)
    (trans (cong (_* (q * u + r * v)) (*-inverseʳ m {{≢-nonZero nz}}))
      (*-identityˡ (q * u + r * v)))
    where
    rearrange : ∀ m q r u v i → m * (q * i * u + r * i * v) ≡ (m * i) * (q * u + r * v)
    rearrange = solve 6 (λ m q r u v i →
      m :* (q :* i :* u :+ r :* i :* v) := (m :* i) :* (q :* u :+ r :* v)) refl
      where open +-*-Solver

  chooseList-correct : (fallback : A) (xs : List (ℚ × A)) (ns : NonNeg-L xs) (P : A → ℚ)
    → mass-L xs * lookupᴰℚ (entries (sample (chooseList fallback xs ns))) P ≡ weighted xs P
  chooseList-correct fallback [] All.[] P = *-zeroˡ (lookupᴰℚ (entries (return-ℚ fallback)) P)
  chooseList-correct fallback ((q , x) ∷ []) (n All.∷ All.[]) P = trans
    (cong₂ _*_ (+-identityʳ q) (lookupᴰℚ-return x P)) (sym (+-identityʳ (q * P x)))
  chooseList-correct fallback ((q , x) ∷ xs@(e ∷ rest)) (n All.∷ ns) P with (q + mass-L xs) ≟ 0ℚ
  ... | yes z = trans (cong (_* lookupᴰℚ (entries (return-ℚ fallback)) P) z)
    (trans (*-zeroˡ (lookupᴰℚ (entries (return-ℚ fallback)) P))
      (sym (zero-weighted ((q , x) ∷ xs) (n All.∷ ns) z P)))
  ... | no nz = trans (cong ((q + mass-L xs) *_) expectation)
    (trans (cancel-scale (q + mass-L xs) q (mass-L xs) (P x) _ nz)
      (cong (q * P x +_) (chooseList-correct fallback xs ns P)))
    where
    κ = chooseList fallback xs ns
    μ = split q (mass-L xs) n (mass-nn xs ns) nz
    expectation : lookupᴰℚ (entries (sample (toss μ (λ where false → done x ; true → κ)))) P
      ≡ q * (1/ (q + mass-L xs)) {{≢-nonZero nz}} * P x
        + mass-L xs * (1/ (q + mass-L xs)) {{≢-nonZero nz}} * lookupᴰℚ (entries (sample κ)) P
    expectation = trans (lookupᴰℚ-bind (entries μ)
      (λ where false → entries (return-ℚ x) ; true → entries (sample κ)) P)
      (cong₂ _+_ (cong ((q * (1/ (q + mass-L xs)) {{≢-nonZero nz}}) *_)
        (lookupᴰℚ-return x P)) (+-identityʳ _))

rationalCoins : Dist-ℚ A → Coins A
rationalCoins μ = chooseList (proj₂ (NE.head (entries μ))) (NE.toList (entries μ)) (weights-nn μ)

rationalCoins-correct : (μ : Dist-ℚ A) → sample (rationalCoins μ) ≈Mℚ μ
rationalCoins-correct μ P = trans (sym (*-identityˡ e))
  (trans (cong (_* e) (sym (mass-1 μ)))
    (chooseList-correct (proj₂ (NE.head (entries μ))) (NE.toList (entries μ)) (weights-nn μ) P))
  where e = lookupᴰℚ (entries (sample (rationalCoins μ))) P
