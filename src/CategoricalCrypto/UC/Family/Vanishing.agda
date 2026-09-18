{-# OPTIONS --safe --without-K #-}

-- The vanishing tier's agreement, in the INHERITED order.
--
-- The gap this closes: `UC.Family.absorb` lands in the ancilla-quantified
-- `_≈ℰ_` of `UC.Environment UCBase^ω`, while the same statement at `ucSetup^ω`
-- would land in `Abstract2._≈ᵁ_`, and the kernel congruence is a
-- `no-eta-equality` record, so re-basing `absorb` in place would change its
-- stated type.  So it is not re-based — the bridge is applied to its result
-- instead, which changes nothing that already exists.
--
-- `UC.Core.Bridge` is already generic in the monoidal base and the
-- observation, so the whole content here is `rel-agree^ω`: that the bridge's
-- kernel is this tier's own `_≈ℰ_` and not a parallel spelling.  Its
-- counterpart one tier over is `UC.Family.Negligible.Setup`.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.UC.Approximate using (ApproximateObservation; ℚ-errors)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Core using (Observation)

import CategoricalCrypto.UC.Core.Bridge as Bridgeᴹ
import CategoricalCrypto.UC.Core.Standard as Std

module CategoricalCrypto.UC.Family.Vanishing
  {o ℓ e os ℓs ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (obsᴹ : Observation (MonoidalCategory.U M) os ℓs)
  (qapx : ApproximateObservation obsᴹ ℚ-errors ℓa)
  (bud : Budget (MonoidalCategory.U M) (Std.gradingᵗ M) qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

open import CategoricalCrypto.UC.Family M obsᴹ qapx bud Ix κ κ-cofinal
  using (Famᴹ; Observation^ω; _≈ℰ_)

module Canonical^ω = Bridgeᴹ Famᴹ Observation^ω

-- The tier's own kernel is the bridge's source, on the nose: the base the
-- bridge builds out of `Famᴹ` and `Observation^ω` is `UCBase^ω` itself.
rel-agree^ω : {A B : Canonical^ω.Channel} {f g : Canonical^ω._⇒_ A B}
            → (Canonical^ω._≈ℰᶜ_ f g) ≡ (f ≈ℰ g)
rel-agree^ω = refl

-- …so a vanishing bound, once absorbed, is a witness for the inherited order.
-- The homs are explicit for `UC.Family.Negligible.≈ℰⁿ⇒≈ℰᴺ`'s measured reason.
≈ℰ^ω⇒≤UC : {A B X : Canonical^ω.Channel}
           (f g : Canonical^ω._⇒_ A (Canonical^ω.T₀ X B))
         → f ≈ℰ g → Canonical^ω._≤UC_ f g
≈ℰ^ω⇒≤UC f g = Canonical^ω.≈ℰᶜ⇒≤UC
