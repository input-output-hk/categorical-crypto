{-# OPTIONS --safe --without-K #-}

-- The vanishing tier read off ONE quantitative setup at the family category
-- (`docs/quantitative-uc-setup-plan.typ` §§3, 9).
--
-- `UC.Quantitative.Observed` at `Famᴹ` over scalar rational errors supplies the
-- test presheaf; forgetting it along `F₊` gives `ucSetup^ω` back.  The two
-- presheaves do NOT coincide by head — `_≋_` quantifies the closure first and
-- `_∼ᵃ_` the error first — so what identifies them is that exchange, `≋⇔∼₊`;
-- `Abstract2.Morphism.Refine` is what carries it from the bare kernel to the
-- emulation order with the simulator unchanged.
--
-- The instance reaches `Standard2.StdUC Famᴹ` at `Evaluation^ω`'s test
-- presheaf, which `UC.Family.Vanishing.Canonical^ω` already is, so the order
-- below is the tier's own and not a parallel spelling.
--
-- The local-negligible counterpart is `UC.Family.Negligible.Quantitative`,
-- split off as `UC.Family.Vanishing` and `UC.Family.Negligible.Setup` are.

open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.Abstract2.Morphism using (module Refine)
open import CategoricalCrypto.Approx.Error using (module AllPositive; ℚ-ordered; ℚ-refinement)
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered using (QEvaluation)
open import CategoricalCrypto.UCSetup using (UCSetup)

import CategoricalCrypto.UC.Family.Vanishing as Vanᴹ
import CategoricalCrypto.UC.Quantitative.Observed as Observedᴹ

module Rates = SymmetricMonoidalCategory Rates

module CategoricalCrypto.UC.Family.Quantitative
  {o ℓ e os ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (qro : QEvaluation (MonoidalCategory.U M) os ℓa)
  (Rg : GradedSubCat Rates.monoidalCategory M qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

open import CategoricalCrypto.UC.Family M qro Rg Ix κ κ-cofinal
  using (Famᴹ; QEvaluation^ω)

-- Each private application copies only what its `using` list names: a whole
-- `StdUC` or `AbstractUC` copied under this module's telescope cost 0.7 GB of
-- the root's heap here.
private
  module C^ω = Vanᴹ.Canonical^ω M qro Rg Ix κ κ-cofinal
    using (Channel; _⇒_; T₀; _∘_; _≈ᵁ_; _≤UC_; StdSetup; module KE)
  module P^ω = AllPositive ℚ-refinement (QEvaluation.approx QEvaluation^ω)
    using (∼ᵃ-isEquivalence; zero⇒positive)

-- Spelled exactly as `Approx.Evaluation.qual₊` spells it, so the readout this
-- lands at IS `Evaluation^ω` and `C^ω` is the setup it is compared with.
module Q^ω = Observedᴹ Famᴹ ℚ-ordered QEvaluation^ω P^ω.∼ᵃ-isEquivalence P^ω.zero⇒positive

-- `Evaluation^ω` is `qual₊`'s, so `_∼_` IS eventual closeness at every positive
-- error and both comparisons with it are the identity.
open Q^ω.AllPositive ℚ-refinement using (module Absorbing)
open Absorbing (λ h → h) public
open Reflecting (λ h → h) public

setup₊ : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (ℓ ⊔ qs) (ℓ ⊔ qs ⊔ ℓa)
setup₊ = Q^ω.Quant.underlying₊ ℚ-refinement

-- Tests and homs are supplied explicitly throughout, for the measured reason
-- `UC.Family.Negligible.≈ℰⁿ⇒≈ℰᴺ` records.
private
  module A₊ = Q^ω.Quant.AllPositive.A₊ ℚ-refinement using (_≈ᵁ_; _≤UC_; module KE)
  module R₊  = Refine C^ω.StdSetup (UCSetup.ℰ setup₊)
                 (λ {D} {_} {f} {g} h → A₊.KE.mk∼ λ {t} →
                    ≋⇒∼₊ {A = D} {t C^ω.∘ f} {t C^ω.∘ g} (C^ω.KE.run∼ h {t}))
  module R^ω = Refine setup₊ (UCSetup.ℰ C^ω.StdSetup)
                 (λ {D} {_} {f} {g} h → C^ω.KE.mk∼ λ {t} →
                    ∼₊⇒≋ {A = D} {t C^ω.∘ f} {t C^ω.∘ g} (A₊.KE.run∼ h {t}))

≈ᵁ^ω⇒≈ᵁ₊ : {A B X : C^ω.Channel} (f g : C^ω._⇒_ A (C^ω.T₀ X B))
         → C^ω._≈ᵁ_ f g → A₊._≈ᵁ_ f g
≈ᵁ^ω⇒≈ᵁ₊ f g = R₊.≈ᵁ-refine {f = f} {g = g}

≈ᵁ₊⇒≈ᵁ^ω : {A B X : C^ω.Channel} (f g : C^ω._⇒_ A (C^ω.T₀ X B))
         → A₊._≈ᵁ_ f g → C^ω._≈ᵁ_ f g
≈ᵁ₊⇒≈ᵁ^ω f g = R^ω.≈ᵁ-refine {f = f} {g = g}

≈ᵁ^ω⇔≈ᵁ₊ : {A B X : C^ω.Channel} (f g : C^ω._⇒_ A (C^ω.T₀ X B))
         → (C^ω._≈ᵁ_ f g) ⇔ (A₊._≈ᵁ_ f g)
≈ᵁ^ω⇔≈ᵁ₊ f g = mk⇔ (≈ᵁ^ω⇒≈ᵁ₊ f g) (≈ᵁ₊⇒≈ᵁ^ω f g)

-- Bundling the two below as one `⇔` costs 22 s to elaborate their type a third
-- time, against 8 s for the agreement bundle above, so they stand alone.
≤UC^ω⇒≤UC₊ : {A B X Y : C^ω.Channel}
             (f : C^ω._⇒_ A (C^ω.T₀ X B)) (g : C^ω._⇒_ A (C^ω.T₀ Y B))
           → C^ω._≤UC_ f g → A₊._≤UC_ f g
≤UC^ω⇒≤UC₊ f g = R₊.≤UC-refine {f = f} {g = g}

≤UC₊⇒≤UC^ω : {A B X Y : C^ω.Channel}
             (f : C^ω._⇒_ A (C^ω.T₀ X B)) (g : C^ω._⇒_ A (C^ω.T₀ Y B))
           → A₊._≤UC_ f g → C^ω._≤UC_ f g
≤UC₊⇒≤UC^ω f g = R^ω.≤UC-refine {f = f} {g = g}
