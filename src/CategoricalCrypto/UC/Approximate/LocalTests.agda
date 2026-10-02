{-# OPTIONS --safe --without-K #-}

-- The acceptance criteria of `docs/protocol-implementation-review.md` §1, as
-- theorems: the local negligible agreement ADMITS a one-shot `2⁻ⁿ` difference
-- and REJECTS a one-shot `1/(n+1)` one, the latter being what mere vanishing
-- would let in.
--
-- Read at `Approx.Error.ℚ-metric`, `Ix = ℕ`, `κ` the identity.

open import Data.Integer.Base using (+<+)
open import Data.Nat.Base as ℕ using (ℕ; suc; z≤n; s≤s)
open import Data.Nat.Poly
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Distribution.Uniform.Decay

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Approximate.Decay

import Data.Nat.Properties as ℕₚ

module CategoricalCrypto.UC.Approximate.LocalTests where

open import CategoricalCrypto.UC.Approximate.Local ℚ-metric ℕ (λ n → n)

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

-- …and it DOES vanish: with `¬negligible-inv-suc`, the checked separation of
-- the two grades — `_→0` is strictly weaker than `Negligible`.
inv-suc-→0 : inv-suc →0
inv-suc-→0 ε ε>0 =
  let M , 1≤Mε = archimedean ε>0
  in M , λ n M≤n →
    *-cancelˡ-≤-pos (fromℕ (suc n)) {{positive (0<fromℕ-suc n)}}
      (subst (ℚ._≤ fromℕ (suc n) ℚ.* ε)
             (sym (*-inverseʳ (fromℕ (suc n)) {{nzᶠ n}}))
             (≤-trans 1≤Mε
               (*-monoʳ-≤-nonNeg ε {{nonNegative (<⇒≤ ε>0)}}
                 (fromℕ-mono-≤ (s≤s M≤n)))))

------------------------------------------------------------------------
-- The acceptance criteria

-- The always-safe family both differences are measured against.
zeroᶠ : ℕ → ℚ
zeroᶠ _ = 0ℚ

-- `2⁻ⁿ` is negligible at the identity schedule, and the metric charges exactly
-- the difference: the pair is admitted, error witness and all.
admits-inv-pow-2 : inv-pow-2 ∼ᴺ zeroᶠ
admits-inv-pow-2 = inv-pow-2 , negligible-slack (λ _ → ℕₚ.≤-refl)
                 , λ i → ≈ᵐ-0 (0≤inv-pow-2 i)

-- `1/(n+1)` is not: an admitting witness would dominate the whole gap, and
-- negligibility passes down to what it dominates.
rejects-inv-suc : ¬ (inv-suc ∼ᴺ zeroᶠ)
rejects-inv-suc h =
  let δ , neg , dom = ∼ᴺ-gap inv-suc zeroᶠ inv-suc (λ n → n , refl) ≈ᵐ-gap h
  in ¬negligible-inv-suc (Negligible-≤ dom neg)
