{-# OPTIONS --safe --without-K #-}

-- The negligible tier as a SECOND observation on the family category, and the
-- one-way bridge into it (`docs/graded-observation-redesign.md`).
--
-- `UC.Family`'s closing comment records what it does not deliver: an
-- `Evaluation` whose comparison keeps a negligible error witness, because
-- `qual₊` coarsens by quantifying an ambient ε away.  It is not a core redesign
-- though — `UC.Core.Evaluation` asks for an ARBITRARY setoid, and
-- `Approx.Evaluation.qualBy` coarsens by any equivalence zero error implies,
-- which `UC.Approximate.Local`'s `_∼ᴺ_` is.  So the whole negligible tier is
-- this instance plus the emulation notions inherited at it, and nothing in the
-- qualitative core moves: `Evaluation^ω` and `_≈ᵁ_` are exactly as they were.
--
-- `_≈ℰⁿ_` implies the new relation at every context by SPECIALIZING its global
-- allowance-indexed error to the allowance that context carries — its test
-- certified at its own rate, scaled by its closure's.  The
-- converse does not hold and the two are deliberately not identified: a
-- witness chosen per context is weaker than one global bound, and no
-- uniformization theorem closes the gap (`docs/protocol-implementation-review.md`
-- §4).
--
-- The acceptance criteria of review §1 — a one-shot `2⁻ⁿ` difference admitted,
-- a one-shot `1/(n+1)` difference rejected — are theorems about `_∼ᴺ_` at a
-- separating approximation, proved in `UC.Approximate.LocalTests`.

open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Positive using (_·_; value)
open import Data.Product.Base using (Σ-syntax; _,_)
open import Data.Rational using (0ℚ)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.Approx.Error using (ℚ-ordered)
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered using (QEvaluation)
open import CategoricalCrypto.Approx.Schedule using (pointwise)
open import CategoricalCrypto.UC.Approximate using (Negligible-0)
open import CategoricalCrypto.UC.Core using (Evaluation; Observable)

import CategoricalCrypto.Approx.Evaluation as Evaluationᴹ
import CategoricalCrypto.Standard2 as Std2

module Rates = SymmetricMonoidalCategory Rates

module CategoricalCrypto.UC.Family.Negligible
  {o ℓ e os ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (qro : QEvaluation (MonoidalCategory.U M) os ℓa)
  (Rg : GradedSubCat Rates.monoidalCategory M qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

open import CategoricalCrypto.UC.Family M qro Rg Ix κ κ-cofinal

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
-- (`UC.Family.Negligible.Setup`, and the gate in
-- `docs/retirement-negligible-order.md`).
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
