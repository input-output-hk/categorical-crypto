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
open import Data.Product.Base using (Σ-syntax)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.UC.Approximate using (ApproximateObservation; ℚ-errors)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Core using (Observation)
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
  using (Famᴹ; baseᴹ)

private
  module N = Negᴹ baseᴹ qapx bud Ix κ κ-cofinal

-- The canonical setup, its whole inherited metatheory, and the bridge.
module Canonicalᴺ = Bridgeᴹ Famᴹ N.Observationᴺ

ucSetupᴺ : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (ℓ ⊔ qs) (ℓ ⊔ qs ⊔ ℓa)
ucSetupᴺ = Canonicalᴺ.StdSetup

-- The tier's existing relation is the bridge's source, on the nose.
rel-agree : {A B : Canonicalᴺ.Channel} {f g : Canonicalᴺ._⇒_ A B}
          → (Canonicalᴺ._≈ℰᶜ_ f g) ≡ (N._≈ℰᴺ_ f g)
rel-agree = refl

-- …so the tier's emulation order embeds in the INHERITED one: `UC.Emulation`'s
-- dummy witness is `Abstract2.dummy-complete` applied to the bridged kernel.
-- This is what makes `_≤UCᴺ_` an instance rather than a second definition.
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

-- The tier's ORDER does not embed by this route as it stands.  `_≤UCᴺ_`'s
-- witness is `Grading^ω.sub s ∘ g` and `dummy-complete` wants the Kleisli
-- triple's `sub s ∘ g`; the two agree under `_≈^ω_`, which ignores a carried
-- bound, but closing the gap makes Agda compare the two homs' `Poly`
-- WITNESSES, and those are proof terms it cannot identify.  Retiring
-- `UC.Emulation._≤UC_` at this tier therefore needs the two `sub`s reconciled
-- first — by a propositional equality of the gradings, or by a `Fam` whose
-- hom equality quotients the bound — and not merely this transport.
