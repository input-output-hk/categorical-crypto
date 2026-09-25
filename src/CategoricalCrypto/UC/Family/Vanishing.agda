{-# OPTIONS --safe --without-K #-}

-- The vanishing tier's agreement, in the INHERITED order.
--
-- `Canonical^ω` is `Standard2.StdUC` at `Famᴹ` and `ℰ^ω`, whose `_≈ᵁ_`
-- is the one `UC.Family` re-exports, so what `UC.Family.absorb` concludes is
-- a witness for `Canonical^ω._≤UC_` through `Canonical^ω.≈ᵁ⇒≤UC`.  Its
-- counterpart one tier over is `UC.Family.Negligible.Setup`.

open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax)
open import Level using (Level)

open import CategoricalCrypto.Approx.Error using (ℚ-ordered)
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered using (QEvaluation)

import CategoricalCrypto.Standard2 as Std2

module Rates = SymmetricMonoidalCategory Rates

module CategoricalCrypto.UC.Family.Vanishing
  {o ℓ e os ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (qro : QEvaluation (MonoidalCategory.U M) os ℓa)
  (Rg : GradedSubCat Rates.monoidalCategory M qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

open import CategoricalCrypto.UC.Family M qro Rg Ix κ κ-cofinal
  using (Famᴹ; ℰ^ω)

module Canonical^ω = Std2.StdUC Famᴹ ℰ^ω
