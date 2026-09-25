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
-- in).  `Evaluationᴺ` keeps an error witness of its own, so neither `induces`
-- nor `reflects` is available and the observation enters only through its
-- closed runs — which is what `Observed`'s parameters were cut down to.
--
-- The instance reaches `Standard2.StdUC Famᴹ` at `Evaluationᴺ`'s test
-- presheaf, which `UC.Family.Negligible.Setup.Canonicalᴺ` already is, so the
-- order landed in is the canonical tier's own.
--
-- The vanishing counterpart is `UC.Family.Quantitative`.

open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational using (ℚ; 0ℚ)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.Abstract2.Morphism using (module Refine)
open import CategoricalCrypto.Approx.Error using (ℚ-ordered)
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered using (QEvaluation)
open import CategoricalCrypto.Approx.Schedule using (pointwise)
open import CategoricalCrypto.UC.Approximate using (Negligible; Negligible-0)
open import CategoricalCrypto.UC.Core using (Evaluation; Observable)
open import CategoricalCrypto.UCSetup using (UCSetup)
import CategoricalCrypto.UC.Family.Negligible as Negᴹ
import CategoricalCrypto.UC.Family.Negligible.Setup as Setupᴹ
import CategoricalCrypto.UC.Quantitative.Observed as Observedᴹ

module Rates = SymmetricMonoidalCategory Rates

module CategoricalCrypto.UC.Family.Negligible.Quantitative
  {o ℓ e os ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (qro : QEvaluation (MonoidalCategory.U M) os ℓa)
  (Rg : GradedSubCat Rates.monoidalCategory M qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

open import CategoricalCrypto.UC.Family M qro Rg Ix κ κ-cofinal using (Famᴹ)

private
  module N   = Negᴹ   M qro Rg Ix κ κ-cofinal
  module Set = Setupᴹ M qro Rg Ix κ κ-cofinal
  module Cᴺ  = Set.Canonicalᴺ
  module Qr  = QEvaluation qro
  open Evaluation N.Evaluationᴺ using (Closure; observe)
  open Observable (Evaluation.observable N.Evaluationᴺ) using (Test; _≋_)

-- Spelled exactly as `UC.Family.Negligible.Evaluationᴺ` spells it, so the
-- readout this lands at IS that one and `Cᴺ` is the setup it is compared with.
module Qᴺ = Observedᴹ Famᴹ (pointwise ℕ ℚ-ordered) N.QEvaluationᴺ
                     N.∼ᴺ-isEquivalence (λ h → (λ _ → 0ℚ) , Negligible-0 , h)

private
  module Sm = Qᴺ.Quant.Small N.negligible

setupᴺ⁺ : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (ℓ ⊔ qs) (ℓ ⊔ qs ⊔ ℓa)
setupᴺ⁺ = Qᴺ.Quant.underlyingSmall N.negligible

-- The existential moves INSIDE the closure quantifier, which is what
-- `ucSetupᴺ`'s presheaf compares by.  Nothing brings it back out.
uniform⇒local : {A : Cᴺ.Channel} (E₁ E₂ : Test A)
              → Σ[ δ ∈ (ℕ → ℚ) ] Negligible δ
                  × ((m : Closure A) (i : Ix)
                     → Qr._≈[_]_ (observe E₁ m i) (δ (κ i)) (observe E₂ m i))
              → E₁ ≋ E₂
uniform⇒local E₁ E₂ (δ , neg , h) m = δ , neg , h m

-- Tests and homs are supplied explicitly throughout, for the measured reason
-- `UC.Family.Negligible.≈ℰⁿ⇒≈ℰᴺ` records.
private
  module Rᴺ = Refine setupᴺ⁺ (UCSetup.ℰ Cᴺ.StdSetup)
                (λ {D} {_} {f} {g} h → Cᴺ.KE.mk∼ λ {t} →
                   uniform⇒local {D} (t Cᴺ.∘ f) (t Cᴺ.∘ g) (Sm.Aˢ.KE.run∼ h {t}))

≈ᵁˢ⇒≈ᵁᴺ : {A B X : Cᴺ.Channel} (f g : Cᴺ._⇒_ A (Cᴺ.T₀ X B))
        → Sm.Aˢ._≈ᵁ_ f g → Cᴺ._≈ᵁ_ f g
≈ᵁˢ⇒≈ᵁᴺ f g = Rᴺ.≈ᵁ-refine {f = f} {g = g}

≤UCˢ⇒≤UCᴺ : {A B X Y : Cᴺ.Channel}
            (f : Cᴺ._⇒_ A (Cᴺ.T₀ X B)) (g : Cᴺ._⇒_ A (Cᴺ.T₀ Y B))
          → Sm.Aˢ._≤UC_ f g → Cᴺ._≤UC_ f g
≤UCˢ⇒≤UCᴺ f g = Rᴺ.≤UC-refine {f = f} {g = g}

-- …so a bound at ONE negligible schedule, good at every context, is a witness
-- for the canonical local-negligible order with its simulator unchanged.
uniform-witness⇒≤UCᴺ :
    {A B X Y : Cᴺ.Channel}
    (f : Cᴺ._⇒_ A (Cᴺ.T₀ X B)) (g : Cᴺ._⇒_ A (Cᴺ.T₀ Y B))
  → Σ[ s ∈ Cᴺ._⇒_ Y X ] Σ[ δ ∈ (ℕ → ℚ) ] Negligible δ × Qᴺ.Quant.At s δ f g
  → Cᴺ._≤UC_ f g
uniform-witness⇒≤UCᴺ f g w = ≤UCˢ⇒≤UCᴺ f g (Sm.small-emulation⇐ {f = f} {g} w)
