{-# OPTIONS --safe --without-K #-}

-- The canonical LOCAL-NEGLIGIBLE `UCSetup`, and the bridge into it
-- (`docs/quantitative-uc-setup-plan.typ` §9's `local-negligible⇔canonical`).
--
-- `UC.Family.ucSetup^ω` is `Famᴹ` at `Evaluation^ω`, whose comparison has
-- quantified its error away.  This is the same four fields at
-- `UC.Family.Negligible.Evaluationᴺ`, whose comparison KEEPS a negligible
-- witness, so the whole of `Abstract2` — `≤UC-refl`, `dummy-complete`,
-- `≤UC-trans`, `UC-compose`, `≈ᵁ⇒≈ℰ` — is inherited at the negligible tier
-- instead of being restated there.
--
-- Both the setup and the bridge are `Standard2.StdUC` at the readout's test
-- presheaf, already generic in the monoidal base, applied here, and its `_≈ᵁ_`
-- is the tier's `_≈ℰᴺ_`.

open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.Approx.Error using (ℚ-ordered)
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered using (QEvaluation)
open import CategoricalCrypto.UC.Core using (Evaluation; Observable)
open import CategoricalCrypto.UCSetup using (UCSetup)

import CategoricalCrypto.Standard2 as Std2
import CategoricalCrypto.UC.Family.Negligible as Negᴹ

module Rates = SymmetricMonoidalCategory Rates

module CategoricalCrypto.UC.Family.Negligible.Setup
  {o ℓ e os ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (qro : QEvaluation (MonoidalCategory.U M) os ℓa)
  (Rg : GradedSubCat Rates.monoidalCategory M qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

open import CategoricalCrypto.UC.Family M qro Rg Ix κ κ-cofinal
  using (Famᴹ; ucSetup^ω; _≈ℰⁿ_)

private module N = Negᴹ M qro Rg Ix κ κ-cofinal

-- The canonical setup, its whole inherited metatheory, and the bridge.
module Canonicalᴺ = Std2.StdUC Famᴹ (Observable.ℰᴼ (Evaluation.observable N.Evaluationᴺ))

ucSetupᴺ : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (ℓ ⊔ qs) (ℓ ⊔ qs ⊔ ℓa)
ucSetupᴺ = Canonicalᴺ.StdSetup

-- A concrete budget-indexed bound reaches the INHERITED order directly: the
-- tier's own ingestion composed with the bridge, with `≤UC-trans`,
-- `dummy-complete` and `UC-compose` behind it.  The homs are EXPLICIT, for
-- `UC.Family.Negligible.≈ℰⁿ⇒≈ℰᴺ`'s measured reason: both orders read them
-- under an application, so inference would elaborate each carried polynomial
-- as a meta.
≈ℰⁿ⇒≤UC : {A B X : Canonicalᴺ.Channel}
          (f g : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ X B))
        → f ≈ℰⁿ g → Canonicalᴺ._≤UC_ f g
≈ℰⁿ⇒≤UC f g h = Canonicalᴺ.≈ᵁ⇒≤UC {f = f} {g} (N.≈ℰⁿ⇒≈ℰᴺ f g h)

-- `ucSetup^ω` is the VANISHING one — `Evaluation^ω`'s comparison is vanishing
-- advantage, `Approx.Evaluation.qual₊` having quantified the error away — and
-- `ucSetupᴺ` is the LOCAL-NEGLIGIBLE one, which keeps the witness.  They
-- differ in the presheaf and in nothing else, which is what makes them two
-- readings of one computational structure rather than two theories: the
-- category, the grades and the graded monad are shared.
shared-computational :
    (UCSetup.𝒞 ucSetup^ω ≡ UCSetup.𝒞 ucSetupᴺ)
  × (UCSetup.ℐ ucSetup^ω ≡ UCSetup.ℐ ucSetupᴺ)
  × (UCSetup.ℳ ucSetup^ω ≡ UCSetup.ℳ ucSetupᴺ)
shared-computational = refl , refl , refl
