{-# OPTIONS --safe --without-K #-}

-- The local-negligible tier against ONE quantitative setup at the family
-- category (`docs/quantitative-uc-setup-plan.typ` §8).
--
-- `UC.Quantitative.Observed` at `Famᴹ` over SCHEDULE errors supplies the test
-- presheaf; forgetting it along `Approx.Small`'s negligible collapse gives the
-- UNIFORM relation `∃ negligible δ. ∀ closure. …`.  `ucSetupᴺ`'s presheaf is
-- the LOCAL one, `∀ closure. ∃ negligible δ. …`, so the two are NOT the same
-- setup: only the transfer into the local one is a theorem here, and the
-- converse is the uniformization plan §8 leaves open
-- (`UC.Approximate.Local.∼ᴺ⇒pointwise` is the same asymmetry one quantifier
-- in).  `Observationᴺ` keeps an error witness of its own, so neither `induces`
-- nor `reflects` is available and the observation enters only through its
-- closed runs — which is what `Observed`'s parameters were cut down to.
--
-- The instance reaches `UC.Core.Bridge Famᴹ Observationᴺ`, which
-- `UC.Family.Negligible.Setup.Canonicalᴺ` already is, so the order landed in is
-- the canonical tier's own; `rel-agree` pins the kernel there.
--
-- The vanishing counterpart is `UC.Family.Quantitative`.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational using (ℚ)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.Approx.Error using (ℚ-ordered)
open import CategoricalCrypto.Approx.Schedule using (pointwise)
open import CategoricalCrypto.UC.Approximate
  using (ApproximateObservation; Negligible; ℚ-errors)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Core using (Observation)
open import CategoricalCrypto.UCSetup using (UCSetup)

import CategoricalCrypto.Abstract2.Action as Action
import CategoricalCrypto.Approx.Space as Spaceᴹ
import CategoricalCrypto.UC.Family.Negligible as Negᴹ
import CategoricalCrypto.UC.Family.Negligible.Setup as Setupᴹ
import CategoricalCrypto.UC.Quantitative.Observed as Observedᴹ

module CategoricalCrypto.UC.Family.Negligible.Quantitative
  {o ℓ e os ℓs ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (obsᴹ : Observation (MonoidalCategory.U M) os ℓs)
  (qapx : ApproximateObservation obsᴹ ℚ-errors ℓa)
  (bud : Budget M qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

open import CategoricalCrypto.UC.Family M obsᴹ qapx bud Ix κ κ-cofinal using (Famᴹ)

private
  module N   = Negᴹ   M obsᴹ qapx bud Ix κ κ-cofinal
  module Set = Setupᴹ M obsᴹ qapx bud Ix κ κ-cofinal
  module Cᴺ  = Set.Canonicalᴺ
  module qa  = ApproximateObservation qapx
  -- Spelled exactly as `UC.Approximate.Local` spells it, so that no definition
  -- of this module's stands between `familySpace` and the record it is.
  module Sp  = Spaceᴹ (pointwise ℕ ℚ-ordered)

module Qᴺ = Observedᴹ Famᴹ (pointwise ℕ ℚ-ordered) N.Observationᴺ
                     (Sp.ApproxSpace.approx N.familySpace)
                     (λ eq i → qa.⟦⟧-resp-≈₀ (eq i))

private
  module Aᴺ = Action Cᴺ.StdSetup
  module Sm = Qᴺ.Quant.Small N.negligible

setupᴺ⁺ : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (ℓ ⊔ qs) (ℓ ⊔ qs ⊔ ℓa)
setupᴺ⁺ = Qᴺ.Quant.underlyingSmall N.negligible

-- The existential moves INSIDE the closure quantifier, which is what
-- `ucSetupᴺ`'s presheaf compares by.  Nothing brings it back out.
uniform⇒local : {A : Cᴺ.Channel} (E₁ E₂ : Cᴺ.C.Test A)
              → Σ[ δ ∈ (ℕ → ℚ) ] Negligible δ
                  × ((m : Cᴺ.C.Closure A) (i : Ix)
                     → qa._≈[_]_ (Cᴺ.C.obs E₁ m i) (δ (κ i)) (Cᴺ.C.obs E₂ m i))
              → E₁ Cᴺ.C.≋ E₂
uniform⇒local _ _ (δ , neg , h) m = δ , neg , h m

-- The implicit runs are supplied throughout for `UC.Family.Negligible`'s
-- measured reason: a relation over `Fam` homs reads them under an application,
-- so inference elaborates each carried polynomial as a meta.
≈ᵁˢ⇒≈ᵁᴺ : {A B X : Cᴺ.Channel} (f g : Cᴺ._⇒_ A (Cᴺ.T₀ X B))
        → Sm.Aˢ._≈ᵁ_ f g → Cᴺ._≈ᵁ_ f g
≈ᵁˢ⇒≈ᵁᴺ {A} f g h = Aᴺ.runs⇒≈ᵁ {f = f} {g = g} λ W t →
  uniform⇒local {A = Cᴺ.T₀ W A} (Aᴺ.run W f t) (Aᴺ.run W g t)
                (Sm.Aˢ.run-resp-≈ᵁ {f = f} {g = g} h W t)

≤UCˢ⇒≤UCᴺ : {A B X Y : Cᴺ.Channel}
            (f : Cᴺ._⇒_ A (Cᴺ.T₀ X B)) (g : Cᴺ._⇒_ A (Cᴺ.T₀ Y B))
          → Sm.Aˢ._≤UC_ f g → Cᴺ._≤UC_ f g
≤UCˢ⇒≤UCᴺ f g le =
  let s , h = Sm.Aˢ.≤UC⇒dummy le
  in Cᴺ.dummy-complete (s , ≈ᵁˢ⇒≈ᵁᴺ f (Cᴺ.sub s Cᴺ.∘ g) h)

-- …so a bound at ONE negligible schedule, good at every context, is a witness
-- for the canonical local-negligible order with its simulator unchanged.
uniform-witness⇒≤UCᴺ :
    {A B X Y : Cᴺ.Channel}
    (f : Cᴺ._⇒_ A (Cᴺ.T₀ X B)) (g : Cᴺ._⇒_ A (Cᴺ.T₀ Y B))
  → Σ[ s ∈ Cᴺ._⇒_ Y X ] Σ[ δ ∈ (ℕ → ℚ) ] Negligible δ × Qᴺ.Quant.At s δ f g
  → Cᴺ._≤UC_ f g
uniform-witness⇒≤UCᴺ f g w = ≤UCˢ⇒≤UCᴺ f g (Sm.small-emulation⇐ w)
