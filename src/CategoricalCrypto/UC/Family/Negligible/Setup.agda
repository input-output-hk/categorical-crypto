{-# OPTIONS --safe --without-K #-}

-- The canonical LOCAL-NEGLIGIBLE `UCSetup`, and the bridge into it
-- (`docs/quantitative-uc-setup-plan.typ` §9's `local-negligible⇔canonical`).
--
-- `UC.Family.Monoidal.ucSetup^ω` is `Famᴹ` at `Observation^ω`, whose
-- comparison has quantified its error away.  This is the same four fields at
-- `UC.Family.Negligible.Observationᴺ`, whose comparison KEEPS a negligible
-- witness, so the whole of `Abstract2` — `≤UC-refl`, `dummy-complete`,
-- `≤UC-trans`, `UC-compose`, `≈ᵁ⇒≈ℰ` — is inherited at the negligible tier
-- instead of being restated there.
--
-- Both the setup and the bridge are `UC.Core.Bridge`, already generic in the
-- monoidal base and the observation, applied here.  The one thing that has to
-- be checked is that its ancilla-quantified kernel is the family tier's own
-- `_≈ℰᴺ_` and not a parallel spelling: the two GRADINGS differ (the standard
-- one of `Famᴹ` multiplies a budget where `Grading^ω` does not), but a budget
-- never reaches the observation — `Observationᴺ.⟦_⟧` projects the base
-- component out — so the relations can still coincide.  `rel-agree` is that
-- check.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.UC.Approximate using (ApproximateObservation; ℚ-errors)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Core using (Grading; Observation)
open import CategoricalCrypto.UCSetup using (UCSetup)

import CategoricalCrypto.UC.Core.Bridge as Bridgeᴹ
import CategoricalCrypto.UC.Core.Standard as Std
import CategoricalCrypto.UC.Family.Negligible as Negᴹ

module CategoricalCrypto.UC.Family.Negligible.Setup
  {o ℓ e os ℓs ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (obsᴹ : Observation (MonoidalCategory.U M) os ℓs)
  (qapx : ApproximateObservation obsᴹ ℚ-errors ℓa)
  (bud : Budget (MonoidalCategory.U M) (Std.gradingᵗ M) qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

open import CategoricalCrypto.UC.Family.Monoidal M obsᴹ qapx bud Ix κ κ-cofinal
  using (Famᴹ; baseᴹ; ucSetup^ω; _≈ℰⁿ_; Grading^ω)

private
  module N   = Negᴹ baseᴹ qapx bud Ix κ κ-cofinal
  module GrT = Grading Grading^ω
  module 𝕄   = MonoidalCategory M

-- The canonical setup, its whole inherited metatheory, and the bridge.
module Canonicalᴺ = Bridgeᴹ Famᴹ N.Observationᴺ

ucSetupᴺ : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (ℓ ⊔ qs) (ℓ ⊔ qs ⊔ ℓa)
ucSetupᴺ = Canonicalᴺ.StdSetup

------------------------------------------------------------------------
-- The two canonical instances, side by side

-- `ucSetup^ω` is the VANISHING one — `Observation^ω`'s `_∼_` is vanishing
-- advantage, `UC.Approximate.Induced` having quantified the error away — and
-- `ucSetupᴺ` is the LOCAL-NEGLIGIBLE one, which keeps the witness.  They
-- differ in the presheaf and in nothing else, which is what makes them two
-- readings of one computational structure rather than two theories: the
-- category, the grades and the graded Kleisli triple are shared.
shared-computational :
    (UCSetup.𝒞 ucSetup^ω ≡ UCSetup.𝒞 ucSetupᴺ)
  × (UCSetup.ℐ ucSetup^ω ≡ UCSetup.ℐ ucSetupᴺ)
  × (UCSetup.ℳ ucSetup^ω ≡ UCSetup.ℳ ucSetupᴺ)
shared-computational = refl , refl , refl

------------------------------------------------------------------------
-- The tier's existing relation is the bridge's source, on the nose.
rel-agree : {A B : Canonicalᴺ.Channel} {f g : Canonicalᴺ._⇒_ A B}
          → (Canonicalᴺ._≈ℰᶜ_ f g) ≡ (N._≈ℰᴺ_ f g)
rel-agree = refl

-- …so the tier's agreement is a witness for the INHERITED order directly:
-- `UC.Emulation`'s dummy witness is `Abstract2.dummy-complete` applied to the
-- bridged kernel, which is why the tier needs no order of its own.
-- The homs are EXPLICIT, for `UC.Family.Negligible.≈ℰⁿ⇒≈ℰᴺ`'s measured
-- reason: both orders read them under an application, so inference would
-- elaborate each carried polynomial as a meta.
--
-- Because `rel-agree` holds definitionally, the bridge needs no transport: a
-- negligible agreement of the tier IS a witness for the inherited order, with
-- `≤UC-trans`, `dummy-complete` and `UC-compose` behind it.
≈ℰᴺ⇒≤UC : {A B X : Canonicalᴺ.Channel}
          (f g : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ X B))
        → N._≈ℰᴺ_ f g → Canonicalᴺ._≤UC_ f g
≈ℰᴺ⇒≤UC f g = Canonicalᴺ.≈ℰᶜ⇒≤UC

-- …and a concrete budget-indexed bound reaches that order directly: the tier's
-- own ingestion composed with the bridge.  This is what replaced the tier's
-- retired `≈ℰⁿ⇒≤UCᴺ`: that landed in `Em UCBaseᴺ`'s order, this lands in the
-- inherited one, with `UC-compose` behind it.
≈ℰⁿ⇒≤UC : {A B X : Canonicalᴺ.Channel}
          (f g : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ X B))
        → f ≈ℰⁿ g → Canonicalᴺ._≤UC_ f g
≈ℰⁿ⇒≤UC f g h = ≈ℰᴺ⇒≤UC f g (N.≈ℰⁿ⇒≈ℰᴺ f g h)

------------------------------------------------------------------------
-- …and so does the tier's ORDER

-- The two spellings of a simulator's action differ in the polynomial they
-- carry — `Grading^ω`'s and the one `Famᴹ`'s Kleisli triple builds — but
-- `_≈^ω_` compares base components, and there they are one morphism.
sub-agree^ω : {X Y A : Canonicalᴺ.Channel} (s : Canonicalᴺ._⇒_ X Y)
            → Canonicalᴺ._≈_ (GrT.sub {A = A} s) (Canonicalᴺ.sub s)
sub-agree^ω s i = 𝕄.Equiv.refl

-- With the tier's own order retired (`docs/retirement-negligible-order.md`),
-- the translation lemma that was its gate evidence is retired with it: there
-- is no longer a second order to translate from.  What replaced it is
-- `≈ℰᴺ⇒≤UC` and `≈ℰⁿ⇒≤UC` above, which land in the inherited order directly.
