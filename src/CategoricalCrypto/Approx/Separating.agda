{-# OPTIONS --safe --without-K #-}

-- The example keeping the two collapses of an approximate space apart: zero
-- error (`Approx.Space.zeroSetoid`) and every positive error
-- (`Approx.Error.AllPositive`).  They differ exactly where a space's error
-- balls are not closed, which is why an exact bound is not asked to respect
-- the coarser equality.  One space is enough: rational sequences compared by
-- EVENTUAL closeness.  `2⁻ⁿ` is eventually within every positive ε of the zero
-- sequence and is never eventually equal to it.

open import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Data.Rational as ℚ
open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Approximate.Decay

import Data.Nat.Properties as ℕₚ
import Data.Rational.Properties as ℚₚ

module CategoricalCrypto.Approx.Separating where

open import CategoricalCrypto.Approx.Space ℚ-ordered

zeroᶠ : ℕ → ℚ
zeroᶠ _ = 0ℚ

Sequences : ApproxSpace 0ℓ 0ℓ
Sequences = record { Carrier = ℕ → ℚ ; approx = Eventually ℚ-metric ℕ (λ n → n) }

open AllPositive ℚ-refinement (ApproxSpace.approx Sequences)

positive-identifies : inv-pow-2 ∼ᵃ zeroᶠ
positive-identifies ε pos =
  let N , bnd = Negligible⇒→0 (negligible-slack (λ _ → ℕₚ.≤-refl)) ε pos
  in N , λ n le → ℚₚ.≤-trans (≈ᵐ-0 (ℚₚ.<⇒≤ (0<inv-pow-2 n))) (bnd n le)

zero-separates : ¬ Setoid._≈_ (zeroSetoid Sequences) inv-pow-2 zeroᶠ
zero-separates (N , bnd) = ℚₚ.<-irrefl refl
  (ℚₚ.<-≤-trans (0<inv-pow-2 N) (≈ᵐ-gap (bnd N ℕₚ.≤-refl)))
