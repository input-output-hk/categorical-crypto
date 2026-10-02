{-# OPTIONS --safe --without-K #-}

-- The example keeping `F₀` and `F₊` apart.
--
-- The two forgetful functors differ exactly where a space's error balls are not
-- closed, and one space is enough to show that they do: rational sequences
-- compared by EVENTUAL closeness.  `2⁻ⁿ` is eventually within every positive ε
-- of the zero sequence and is never eventually equal to it.
--
-- The plan's own witness is the model-level one; this is the same phenomenon on
-- the smallest carrier that exhibits it.

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

open import CategoricalCrypto.Approx.Forget ℚ-ordered ℚ-refinement 0ℓ 0ℓ
open import CategoricalCrypto.Approx.Space ℚ-ordered

zeroᶠ : ℕ → ℚ
zeroᶠ _ = 0ℚ

Sequences : ApproxSpace 0ℓ 0ℓ
Sequences = record { Carrier = ℕ → ℚ ; approx = Eventually ℚ-metric ℕ (λ n → n) }

------------------------------------------------------------------------
-- …and the two forgetful functors disagree on one pair

F₊-identifies : Setoid._≈_ ⟦ Sequences ⟧₊ inv-pow-2 zeroᶠ
F₊-identifies ε pos =
  let N , bnd = Negligible⇒→0 (negligible-slack (λ _ → ℕₚ.≤-refl)) ε pos
  in N , λ n le → ℚₚ.≤-trans (≈ᵐ-0 (ℚₚ.<⇒≤ (0<inv-pow-2 n))) (bnd n le)

F₀-separates : ¬ Setoid._≈_ ⟦ Sequences ⟧₀ inv-pow-2 zeroᶠ
F₀-separates (N , bnd) = ℚₚ.<-irrefl refl
  (ℚₚ.<-≤-trans (0<inv-pow-2 N) (≈ᵐ-gap (bnd N ℕₚ.≤-refl)))
