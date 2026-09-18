{-# OPTIONS --safe --without-K #-}

-- Audit emulation as a cost-certified witness for the INHERITED order
-- (`docs/quantitative-uc-setup-plan.typ` §9's `audit⇔canonical`).
--
-- `UC.Audit._≤UC[ cs ]_` is a simulator, its query budget, and an agreement in
-- the ancilla-quantified kernel.  `UC.Core.Bridge` carries that kernel into
-- `Abstract2._≈ᵁ_`, so the same triple is a witness for the inherited order —
-- the simulator and its certificate are carried across untouched, which is the
-- whole point: forgetting the cost evidence is not part of the identification.
--
-- Unlike the family tier, nothing here has to reconcile two spellings of
-- `sub`: at a plain monoidal base the grading's action and the Kleisli
-- triple's are the same morphism, which `sub-agree` records.  At `Fam` they
-- are not, because a `Fam`-hom carries a polynomial bound and the two
-- constructions compute different ones.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.UC.Approximate using (Mass)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Core using (Grading; Observation)

import CategoricalCrypto.UC.Core.Standard as Std

module CategoricalCrypto.UC.Audit.Canonical
  {o ℓ e os ℓs qs : Level}
  (M : MonoidalCategory o ℓ e)
  (O : Observation (MonoidalCategory.U M) os ℓs)
  (bud : Budget (MonoidalCategory.U M) (Std.gradingᵗ M) qs)
  (mass : Mass O)
  where

open import CategoricalCrypto.UC.Core.Bridge M O
open import CategoricalCrypto.UC.Audit baseᵗ bud mass
open Budget bud using (QB)

private
  module G = Grading (Std.gradingᵗ M)

-- The grading's action and the Kleisli triple's are one morphism here.
sub-agree : {X Y A : Channel} {s : X ⇒ Y} → G.sub {A = A} s ≡ sub s
sub-agree = refl

------------------------------------------------------------------------
-- …so an audit emulation IS a cost-certified witness for the inherited order

AuditWitness : {A B X Y : Channel} (cs : ℕ) (f : A ⇒ T₀ X B) (g : A ⇒ T₀ Y B)
             → Set (o ⊔ ℓ ⊔ ℓs ⊔ qs)
AuditWitness {X = X} {Y = Y} cs f g = Σ[ s ∈ (Y ⇒ X) ] (QB cs s × (f ≈ᵁ (sub s ∘ g)))

audit⇒witness : {A B X Y : Channel} {cs : ℕ} {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B}
              → f ≤UC[ cs ] g → AuditWitness cs f g
audit⇒witness e = sim e , sim-qb e , ≈ℰᶜ⇒≈ᵁ (emulate e)

-- Forgetting the cost evidence lands in the inherited order — and it is a
-- SEPARATE step, not part of the identification above.
audit-forget : {A B X Y : Channel} {cs : ℕ} {f : A ⇒ T₀ X B} {g : A ⇒ T₀ Y B}
             → AuditWitness cs f g → f ≤UC g
audit-forget (s , _ , h) = dummy-complete (s , h)
