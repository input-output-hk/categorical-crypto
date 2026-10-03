{-# OPTIONS --safe --without-K #-}

-- The query-sensitive test model as a filtered space.
--
-- Tests are compared through CERTIFIED closures, at a schedule read off the
-- closure's own rate.  Pulling a test back along a morphism of rate `r` moves
-- BOTH indices, and each move is one law of the resource grading: the closure
-- `h ∘ m` is the graded composite at `r′ · r`, so the schedule is reindexed by
-- `_· r`, and the test `E ∘ h` is the graded composite at `q · r`, so the
-- admitted allowance is reindexed by `_· r` too.  That is exactly a
-- `Approx.Filtered` map, error control and allowance map together.
--
-- `pullᵠ` therefore takes a RATED morphism: an arbitrary morphism induces no
-- controlled map on bounded tests, and a control has to be determined by the
-- morphism.  Closure schedules and test allowances are both indexed by `ℕ⁺`,
-- so no schedule is read at a rate no certificate has.  Only the non-tensor part
-- of the graded subcategory is spent.

open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level
open import Relation.Binary.Morphism.Bundles

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered
open import CategoricalCrypto.Approx.Schedule

import CategoricalCrypto.Approx.Filtered as Filteredᴹ
import CategoricalCrypto.Approx.Space as Spaceᴹ
import Data.Nat.Properties as ℕₚ

module CategoricalCrypto.UC.Quantitative.Query where

-- Schedules in the closure rate.
Sched = pointwise ℕ⁺ ℚ-ordered

-- One application, shared with the consumers (`UC.Quantitative.Contextual`):
-- a second one would make every crossing pay for re-elaborating it.
module Fl = Filteredᴹ Sched ≤⁺-poset

open OrderedErrorAlgebra Sched

open Reindexing {I = ℕ⁺} ℚ-ordered

module Tests
  {o ℓ e os ℓa qs : Level} (M : MonoidalCategory o ℓ e)
  (Rg : GradedSubCat Rates.monoidalCategory M qs)
  (qro : QEvaluation (MonoidalCategory.U M) os ℓa) where

  open QEvaluation qro renaming (J to 𝟙)

  open MonoidalCategory M
  open GradedSubCat Rg
  module L = LocallyGradedCategory L

  private
    module Sp = Spaceᴹ Sched

  Test Closure : Obj → Set ℓ
  Test C    = C ⇒ Ω
  Closure C = 𝟙 ⇒ C

  -- A certificate read as the graded hom it certifies, whose interpretation is
  -- the certified morphism ON THE NOSE: `pred-resp` moves the certificate, so
  -- no consumer transports along the certificate's equation.
  certifiedᴴ : {r : ℕ⁺} {C D : Obj} {h : C ⇒ D} → Image forget r h → L.Hom r C D
  certifiedᴴ {h = h} (ĥ , ĥ≈h) = record { arr = h ; Parr = pred-resp ĥ≈h (Predicate.Parr ĥ) }

  ------------------------------------------------------------------------
  -- Tests at a schedule

  infix 4 _≈ᵠ[_]_

  _≈ᵠ[_]_ : {C : Obj} → Test C → (ℕ⁺ → ℚ) → Test C → Set (ℓ ⊔ e ⊔ ℓa ⊔ qs)
  _≈ᵠ[_]_ {C} E τ F =
    (m : Closure C) (r′ : ℕ⁺) → Image forget r′ m → read (E ∘ m) ≈[ τ r′ ] read (F ∘ m)

  approxᵠ : (C : Obj)
          → Approximation (Test C) Sched (ℓ ⊔ e ⊔ ℓa ⊔ qs)
  approxᵠ C = record
    { _≈[_]_    = _≈ᵠ[_]_
    ; ≈[]-refl  = λ _ _ _ → ≈[]-refl
    ; ≈[]-sym   = λ h m r′ cm → ≈[]-sym (h m r′ cm)
    ; ≈[]-trans = λ h k m r′ cm → ≈[]-trans (h m r′ cm) (k m r′ cm)
    ; ≈[]-mono  = λ le h m r′ cm → ≈[]-mono (le r′) (h m r′ cm)
    }

  spaceᵠ : Obj → Sp.ApproxSpace ℓ (ℓ ⊔ e ⊔ ℓa ⊔ qs)
  spaceᵠ C = record { Carrier = Test C ; approx = approxᵠ C }

  -- …and the filtration: which allowance admits which test.
  filteredᵠ : Obj → Fl.FilteredSpace ℓ (ℓ ⊔ e ⊔ ℓa ⊔ qs) (ℓ ⊔ e ⊔ qs)
  filteredᵠ C = record
    { space = spaceᵠ C ; Admit = λ q E → Image forget q E
    ; admit-mono = λ le (Ê , Ê≈E) → L.sub[ le ] Ê , Ê≈E }

  ------------------------------------------------------------------------
  -- Pullback moves both indices, each by one law of the grading

  pullᵠ : {C D : Obj} → Σ[ r ∈ ℕ⁺ ] L.Hom r C D → Fl.Filtered (filteredᵠ D) (filteredᵠ C)
  pullᵠ (r , ĥ) = record
    { underlying = record
        { map     = λ E → E ∘ ⌊ ĥ ⌋
        ; control = reindex (_· r)
        ; preserves = λ hyp n r″ (n̂ , n̂≈n) →
            ≈[]-resp₀ ℚ-ordered approx (read-resp₀ assoc) (read-resp₀ sym-assoc)
              (hyp (⌊ ĥ ⌋ ∘ n) (r″ · r) (ĥ L.∙ n̂ , ∘-resp-≈ʳ n̂≈n))
        }
    ; allowance = mkPosetHomo ≤⁺-poset ≤⁺-poset (_· r) (ℕₚ.*-monoˡ-≤ (value r))
    ; admits = λ {q} (Ê , Ê≈E) →
        L.sub[ ℕₚ.≤-reflexive (ℕₚ.*-comm (value r) (value q)) ] (Ê L.∙ ĥ) , ∘-resp-≈ˡ Ê≈E
    }

