{-# OPTIONS --safe --without-K #-}

-- The negligible tier as a SECOND observation on the family category, and the
-- one-way bridge into it.
--
-- `Approx.Evaluation.qualBy` coarsens by any equivalence zero error implies,
-- and `UC.Approximate.Local`'s `_∼ᴺ_` is one, so the tier is this instance plus
-- the emulation notions inherited at it.
--
-- `_≈ℰⁿ_` implies the new relation at every context by SPECIALIZING its global
-- allowance-indexed error to the allowance that context carries — its test
-- certified at its own rate, scaled by its closure's.  The converse does not
-- hold: a witness chosen per context is weaker than one global bound, and no
-- uniformization theorem closes the gap.  The tier's acceptance criteria are
-- `UC.Approximate.LocalTests`.

open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base as ℕ
open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Rational using (0ℚ)
open import Level

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered
open import CategoricalCrypto.Approx.Schedule
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Core

import CategoricalCrypto.Approx.Evaluation as Evaluationᴹ
import CategoricalCrypto.Standard2 as Std2

module CategoricalCrypto.UC.Family.Negligible
  {o ℓ e os ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (qro : QEvaluation (MonoidalCategory.U M) os ℓa)
  (Rg : GradedSubCat Rates.monoidalCategory M qs)
  (Ix : Set) (κ : Ix → ℕ) where

open import CategoricalCrypto.UC.Family M qro Rg Ix κ

open QEvaluation qro
open GradedSubCat Rg

open import CategoricalCrypto.UC.Approximate.Local approx Ix κ public

------------------------------------------------------------------------
-- The instance

private
  Sched = pointwise ℕ ℚ-ordered
  module RS = Evaluationᴹ Sched

-- The tier's readout: the quantitative one over SCHEDULE errors, coarsened
-- along the negligible collapse rather than along the all-positive one.
QEvaluationᴺ : RS.QEvaluation Fam os ℓa
QEvaluationᴺ = record
  { J = Δ J ; Ω = Δ Ω ; X = familySpace
  ; eval₀ = record
      { to = λ u i → read ⌊ hom u i ⌋ ; cong = λ eq i → read-resp₀ (eq i) }
  }

Evaluationᴺ : Evaluation Fam os ℓa
Evaluationᴺ =
  RS.qualBy QEvaluationᴺ ∼ᴺ-isEquivalence λ h → (λ _ → 0ℚ) , Negligible-0 , h

-- The relation the tier is FOR, renamed apart from `UC.Family`'s.  Its
-- metatheory is not renamed alongside: it is
-- `Standard2.StdUC Famᴹ` at `Evaluationᴺ`'s test presheaf, and a second
-- copy of it under ᴺ names would be the parallel API this tier is meant not to
-- be.  The tier's EMULATION ORDER is `Abstract2`'s at `ucSetupᴺ`
-- (`UC.Family.Negligible.Setup`).
private module N = Std2.StdUC Famᴹ (Observable.ℰᴼ (Evaluation.observable Evaluationᴺ))

open N public using () renaming (_≈ᵁ_ to _≈ℰᴺ_)

------------------------------------------------------------------------
-- The one-way bridge

-- The homs are EXPLICIT for a measured reason: both relations read them under
-- an application, so no value of one determines them by unification, and left
-- to inference the polynomial each carries is elaborated as a meta — 2m25 s of
-- `Poly` arithmetic against 8 s.  The test's rate schedule is explicit for
-- the same reason.
≈ℰⁿ⇒≈ℰᴺ : {A B X : Obj^ω} (f g : A ⇒^ω (X ⊛ω B)) → f ≈ℰⁿ g → f ≈ℰᴺ g
≈ℰⁿ⇒≈ℰᴺ {A} {B} {X} f g (ε , neg , bnd) Y = N.KE.mk∼ λ {Et} m →
  let Et′ = Et N.∘ N.α⇐ {Y} {X}
      Pc  = schedOf-adm Et′ ; c = λ i → hom Et′ i , MonoidalCategory.Equiv.refl M
  in Reassoc.reassoc Evaluationᴺ {A} {B} {X} {Y} Et m {f} {g}
       ( (λ n → ε n (value (schedOf Et′ n · schedOf m n)))
       , neg Y Et′ m {schedOf Et′} Pc c
       , bnd Y Et′ m {schedOf Et′} Pc c )
