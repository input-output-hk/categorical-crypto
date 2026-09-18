{-# OPTIONS --safe --without-K #-}

-- The vanishing tier read off ONE quantitative setup at the family category
-- (`docs/quantitative-uc-setup-plan.typ` §§3, 9).
--
-- `UC.Quantitative.Observed` at `Famᴹ` over scalar rational errors supplies the
-- test presheaf; forgetting it along `F₊` gives `ucSetup^ω` back.  The two
-- presheaves do NOT coincide by head — `_≋_` quantifies the closure first and
-- `_∼ᵃ_` the error first — so what identifies them is that exchange, `≋⇔∼₊`,
-- and it carries all the way to the emulation order with the simulator
-- unchanged.
--
-- The instance reaches `UC.Core.Bridge Famᴹ Observation^ω`, which
-- `UC.Family.Vanishing.Canonical^ω` already is, so the order below is the
-- tier's own and not a parallel spelling; `rel-agree^ω` pins the kernel there.
--
-- The local-negligible counterpart is `UC.Family.Negligible.Quantitative`,
-- split off as `UC.Family.Vanishing` and `UC.Family.Negligible.Setup` are.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax; _,_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.Approx.Error using (ℚ-ordered)
open import CategoricalCrypto.UC.Approximate using (ApproximateObservation; ℚ-errors)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Core using (Observation)
open import CategoricalCrypto.UCSetup using (UCSetup)

import CategoricalCrypto.Abstract2.Action as Action
import CategoricalCrypto.UC.Family.Vanishing as Vanᴹ
import CategoricalCrypto.UC.Quantitative.Observed as Observedᴹ

module CategoricalCrypto.UC.Family.Quantitative
  {o ℓ e os ℓs ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (obsᴹ : Observation (MonoidalCategory.U M) os ℓs)
  (qapx : ApproximateObservation obsᴹ ℚ-errors ℓa)
  (bud : Budget M qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

open import CategoricalCrypto.UC.Family M obsᴹ qapx bud Ix κ κ-cofinal
  using (Famᴹ; Approximate^ω; Observation^ω)

private
  module Van = Vanᴹ M obsᴹ qapx bud Ix κ κ-cofinal
  module C^ω = Van.Canonical^ω
  module a^ω = ApproximateObservation Approximate^ω

-- The implicit runs are supplied throughout for `UC.Family.Negligible`'s
-- measured reason: a relation over `Fam` homs reads them under an application,
-- so inference elaborates each carried polynomial as a meta.
module Q^ω = Observedᴹ Famᴹ ℚ-ordered Observation^ω a^ω.approx
                      (λ {u} {v} → a^ω.⟦⟧-resp-≈₀ {u} {v})

-- `Observation^ω` is `UC.Approximate.Induced`'s, so `_∼_` IS eventual closeness
-- at every positive error and both comparisons with it are the identity.
open Q^ω.Absorbing (λ h → h) public
open Reflecting (λ h → h) public

setup₊ : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (ℓ ⊔ qs) (ℓ ⊔ qs ⊔ ℓa)
setup₊ = Q^ω.Quant.underlying₊

private
  module A^ω = Action C^ω.StdSetup
  module A₊  = Q^ω.Quant.A₊

≈ᵁ^ω⇒≈ᵁ₊ : {A B X : C^ω.Channel} (f g : C^ω._⇒_ A (C^ω.T₀ X B))
         → C^ω._≈ᵁ_ f g → A₊._≈ᵁ_ f g
≈ᵁ^ω⇒≈ᵁ₊ {A} f g h = A₊.runs⇒≈ᵁ {f = f} {g = g} λ W t →
  ≋⇒∼₊ {A = C^ω.T₀ W A} {E₁ = A₊.run W f t} {E₂ = A₊.run W g t}
       (A^ω.run-resp-≈ᵁ {f = f} {g = g} h W t)

≈ᵁ₊⇒≈ᵁ^ω : {A B X : C^ω.Channel} (f g : C^ω._⇒_ A (C^ω.T₀ X B))
         → A₊._≈ᵁ_ f g → C^ω._≈ᵁ_ f g
≈ᵁ₊⇒≈ᵁ^ω {A} f g h = A^ω.runs⇒≈ᵁ {f = f} {g = g} λ W t →
  ∼₊⇒≋ {A = C^ω.T₀ W A} {E₁ = A^ω.run W f t} {E₂ = A^ω.run W g t}
       (A₊.run-resp-≈ᵁ {f = f} {g = g} h W t)

≈ᵁ^ω⇔≈ᵁ₊ : {A B X : C^ω.Channel} (f g : C^ω._⇒_ A (C^ω.T₀ X B))
         → (C^ω._≈ᵁ_ f g) ⇔ (A₊._≈ᵁ_ f g)
≈ᵁ^ω⇔≈ᵁ₊ f g = mk⇔ (≈ᵁ^ω⇒≈ᵁ₊ f g) (≈ᵁ₊⇒≈ᵁ^ω f g)

-- Bundling the two below as one `⇔` costs 22 s to elaborate their type a third
-- time, against 8 s for the agreement bundle above, so they stand alone.
≤UC^ω⇒≤UC₊ : {A B X Y : C^ω.Channel}
             (f : C^ω._⇒_ A (C^ω.T₀ X B)) (g : C^ω._⇒_ A (C^ω.T₀ Y B))
           → C^ω._≤UC_ f g → A₊._≤UC_ f g
≤UC^ω⇒≤UC₊ f g le =
  let s , h = C^ω.≤UC⇒dummy le
  in A₊.dummy-complete (s , ≈ᵁ^ω⇒≈ᵁ₊ f (C^ω.sub s C^ω.∘ g) h)

≤UC₊⇒≤UC^ω : {A B X Y : C^ω.Channel}
             (f : C^ω._⇒_ A (C^ω.T₀ X B)) (g : C^ω._⇒_ A (C^ω.T₀ Y B))
           → A₊._≤UC_ f g → C^ω._≤UC_ f g
≤UC₊⇒≤UC^ω f g le =
  let s , h = A₊.≤UC⇒dummy le
  in C^ω.dummy-complete (s , ≈ᵁ₊⇒≈ᵁ^ω f (C^ω.sub s C^ω.∘ g) h)
