{-# OPTIONS --safe --without-K #-}

-- The acceptance criteria of `docs/protocol-implementation-review.md` §1, as
-- theorems: the local negligible agreement ADMITS a one-shot `2⁻ⁿ` difference
-- and REJECTS a one-shot `1/(n+1)` one, the latter being what mere vanishing
-- would let in.
--
-- Read at `ℚ-metric`, `Ix = ℕ`, `κ` the identity; why the negative half needs a
-- separating approximation is `UC.Approximate.Separating`'s header.

open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Rational
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.UC.Approximate.Decay
open import CategoricalCrypto.UC.Approximate.Separating

module CategoricalCrypto.UC.Approximate.LocalTests where

open import CategoricalCrypto.UC.Approximate.Local ℚ-metric ℕ (λ n → n)

-- The always-safe family both differences are measured against.
zeroᶠ : ℕ → ℚ
zeroᶠ _ = 0ℚ

-- `2⁻ⁿ` is negligible at the identity schedule, and the metric charges exactly
-- the difference: the pair is admitted, error witness and all.
admits-inv-pow-2 : inv-pow-2 ∼ᴺ zeroᶠ
admits-inv-pow-2 = inv-pow-2 , negligible-slack (λ _ → ≤-refl)
                 , λ i → ≈ᵐ-0 (0≤inv-pow-2 i)

-- `1/(n+1)` is not: an admitting witness would dominate the whole gap, and
-- negligibility passes down to what it dominates.
rejects-inv-suc : ¬ (inv-suc ∼ᴺ zeroᶠ)
rejects-inv-suc h =
  let δ , neg , dom = ∼ᴺ-gap inv-suc zeroᶠ inv-suc (λ n → n , refl) ≈ᵐ-gap h
  in ¬negligible-inv-suc (Negligible-≤ dom neg)
