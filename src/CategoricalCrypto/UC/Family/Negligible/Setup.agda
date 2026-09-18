{-# OPTIONS --safe --without-K #-}

-- The canonical LOCAL-NEGLIGIBLE `UCSetup`, and the bridge into it
-- (`docs/quantitative-uc-setup-plan.typ` §9's `local-negligible⇔canonical`).
--
-- `UC.Family.ucSetup^ω` is `Famᴹ` at `Observation^ω`, whose
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
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.UC.Approximate using (ApproximateObservation; ℚ-errors)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Core using (Grading; Observation)
open import CategoricalCrypto.UCSetup using (UCSetup)

import CategoricalCrypto.UC.Core.Bridge as Bridgeᴹ
import CategoricalCrypto.UC.Core.Standard as Std
import CategoricalCrypto.UC.Environment as Env
import CategoricalCrypto.UC.Family.Negligible as Negᴹ

module CategoricalCrypto.UC.Family.Negligible.Setup
  {o ℓ e os ℓs ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (obsᴹ : Observation (MonoidalCategory.U M) os ℓs)
  (qapx : ApproximateObservation obsᴹ ℚ-errors ℓa)
  (bud : Budget (MonoidalCategory.U M) (Std.gradingᵗ M) qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

open import CategoricalCrypto.UC.Family M obsᴹ qapx bud Ix κ κ-cofinal
  using (Famᴹ; ucSetup^ω; _≈ℰⁿ_; Grading^ω)

private
  module N    = Negᴹ M obsᴹ qapx bud Ix κ κ-cofinal
  module Envᴺ = Env N.UCBaseᴺ
  module GrT  = Grading Grading^ω
  module 𝕄    = MonoidalCategory M

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
-- the dummy witness is `Abstract2.dummy-complete` applied to the bridged
-- kernel, which is why the tier needs no order of its own.
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
-- retired `≈ℰⁿ⇒≤UCᴺ`: that landed in the former `_≤UCᵉ_`, this lands in the
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

-- …hence one ideal process, whichever action is put in front of it.  Here and
-- below the implicit homs are supplied for the reason recorded above.
sub-agree^ω-∘ : {A B X Y : Canonicalᴺ.Channel}
                (g : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ Y B))
                (s : Canonicalᴺ._⇒_ Y X)
              → Canonicalᴺ._≈_ (GrT.sub s Canonicalᴺ.∘ g)
                               (Canonicalᴺ.sub s Canonicalᴺ.∘ g)
sub-agree^ω-∘ g s = Canonicalᴺ.∘-resp-≈ˡ
  {f = GrT.sub s} {h = Canonicalᴺ.sub s} {g = g} (sub-agree^ω s)

infix 4 _≤UCᵉ_ _≤UCᵉ⁺_

-- `ᵉ` is the tier's former dummy-form order and its adversary-quantified
-- presentation, recorded here only as the subject of the equivalence below:
-- the two are the same order, `rel-agree` identifying the kernels and
-- `sub-agree^ω` the actions (`docs/retirement-negligible-order.md`).
_≤UCᵉ_ _≤UCᵉ⁺_ : {A B X Y : Canonicalᴺ.Channel}
                 (f : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ X B))
                 (g : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ Y B))
               → Set (o ⊔ ℓ ⊔ qs ⊔ ℓa)
_≤UCᵉ_ {X = X} {Y} f g =
  Σ[ s ∈ Canonicalᴺ._⇒_ Y X ] f N.≈ℰᴺ (GrT.sub s Canonicalᴺ.∘ g)
_≤UCᵉ⁺_ {X = X} {Y} f g =
  {Z : Canonicalᴺ.Channel} (a : Canonicalᴺ._⇒_ X Z)
  → Σ[ s ∈ Canonicalᴺ._⇒_ Y Z ]
      (GrT.sub a Canonicalᴺ.∘ f) N.≈ℰᴺ (GrT.sub s Canonicalᴺ.∘ g)

≈ℰᴺ⇒≈ᵁ-sub : {A B X Y : Canonicalᴺ.Channel}
             (f : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ X B))
             (g : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ Y B))
             (s : Canonicalᴺ._⇒_ Y X)
           → f N.≈ℰᴺ (GrT.sub s Canonicalᴺ.∘ g)
           → f Canonicalᴺ.≈ᵁ (Canonicalᴺ.sub s Canonicalᴺ.∘ g)
≈ℰᴺ⇒≈ᵁ-sub f g s h = Canonicalᴺ.≈ℰᶜ⇒≈ᵁ {f = f} {g = gᵁ}
  (Envᴺ.≈ℰ-trans {f = f} {g = gᵉ} {h = gᵁ} h
    (Envᴺ.≈⇒≈ℰ {f = gᵉ} {g = gᵁ} (sub-agree^ω-∘ g s)))
  where gᵉ = GrT.sub s Canonicalᴺ.∘ g
        gᵁ = Canonicalᴺ.sub s Canonicalᴺ.∘ g

≈ᵁ⇒≈ℰᴺ-sub : {A B X Y : Canonicalᴺ.Channel}
             (f : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ X B))
             (g : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ Y B))
             (s : Canonicalᴺ._⇒_ Y X)
           → f Canonicalᴺ.≈ᵁ (Canonicalᴺ.sub s Canonicalᴺ.∘ g)
           → f N.≈ℰᴺ (GrT.sub s Canonicalᴺ.∘ g)
≈ᵁ⇒≈ℰᴺ-sub f g s h = Envᴺ.≈ℰ-trans {f = f} {g = gᵁ} {h = gᵉ}
  (Canonicalᴺ.≈ᵁ⇒≈ℰᶜ {f = f} {g = gᵁ} h)
  (Envᴺ.≈⇒≈ℰ {f = gᵁ} {g = gᵉ} λ i → 𝕄.Equiv.sym (sub-agree^ω-∘ g s i))
  where gᵉ = GrT.sub s Canonicalᴺ.∘ g
        gᵁ = Canonicalᴺ.sub s Canonicalᴺ.∘ g

≤UCᵉ⇒≤UC : {A B X Y : Canonicalᴺ.Channel}
           (f : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ X B))
           (g : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ Y B))
         → f ≤UCᵉ g → Canonicalᴺ._≤UC_ f g
≤UCᵉ⇒≤UC f g (s , e) = Canonicalᴺ.dummy-complete (s , ≈ℰᴺ⇒≈ᵁ-sub f g s e)

≤UC⇒≤UCᵉ : {A B X Y : Canonicalᴺ.Channel}
           (f : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ X B))
           (g : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ Y B))
         → Canonicalᴺ._≤UC_ f g → f ≤UCᵉ g
≤UC⇒≤UCᵉ f g p = let s , e = Canonicalᴺ.≤UC⇒dummy p in s , ≈ᵁ⇒≈ℰᴺ-sub f g s e

≤UCᵉ⇔≤UC : {A B X Y : Canonicalᴺ.Channel}
           (f : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ X B))
           (g : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ Y B))
         → f ≤UCᵉ g ⇔ Canonicalᴺ._≤UC_ f g
≤UCᵉ⇔≤UC f g = mk⇔ (≤UCᵉ⇒≤UC f g) (≤UC⇒≤UCᵉ f g)

-- The quantified presentation of `ᵉ` needs no separate argument: the canonical
-- order carries the quantifier in its statement, so the adversary's own
-- component is read off it and the two actions reconciled as above.
≤UC⇒≤UCᵉ⁺ : {A B X Y : Canonicalᴺ.Channel}
            (f : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ X B))
            (g : Canonicalᴺ._⇒_ A (Canonicalᴺ.T₀ Y B))
          → Canonicalᴺ._≤UC_ f g → f ≤UCᵉ⁺ g
≤UC⇒≤UCᵉ⁺ f g p a =
  let s , h = p a
      fᵉ = GrT.sub a Canonicalᴺ.∘ f
      fᵁ = Canonicalᴺ.sub a Canonicalᴺ.∘ f
  in s , Envᴺ.≈ℰ-trans {f = fᵉ} {g = fᵁ} {h = GrT.sub s Canonicalᴺ.∘ g}
           (Envᴺ.≈⇒≈ℰ {f = fᵉ} {g = fᵁ} (sub-agree^ω-∘ f a))
           (≈ᵁ⇒≈ℰᴺ-sub fᵁ g s h)
