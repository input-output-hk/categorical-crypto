{-# OPTIONS --safe --without-K #-}

-- `𝒞^ω`, the indexed family layer: `Categories.LocallyGraded.Family` at the
-- `Poly⁺` admissibility over the resource grading, with the negligible
-- observation on top.
-- `κ` must be cofinal, or every eventual statement, hence the whole UC
-- preorder, is vacuously true.
--
-- A cryptographic bound must be NEGLIGIBLE, and mere convergence of the error
-- does not transport that — a bad event of probability `1/(n+1)` vanishes —
-- so the readout is `Approx.Evaluation.qualBy` at `UC.Approximate.Local`'s
-- `_∼ᴺ_`, an equivalence zero error implies, and a statement of that kind
-- keeps its error witness: `_≈ℰⁿ_`.
--
-- `_≈ℰⁿ_` implies the tier's relation `_≈ℰᴺ_` at every context by SPECIALIZING
-- its global allowance-indexed error to the allowance that context carries —
-- its test certified at its own rate, scaled by its closure's.  The converse
-- does not hold: a witness chosen per context is weaker than one global bound,
-- and no uniformization theorem closes the gap.  The tier's acceptance
-- criteria are `UC.Approximate.LocalTests`.

open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded
open import Categories.LocallyGraded.Family
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level

open import ProbabilisticLogic.Distribution.Uniform.Decay

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered
open import CategoricalCrypto.Approx.Schedule
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Evaluation
open import CategoricalCrypto.UCSetup

import CategoricalCrypto.Approx.Evaluation as Evaluationᴹ
import CategoricalCrypto.Standard2 as Std2

module CategoricalCrypto.UC.Family
  {o ℓ e os ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (qro : QEvaluation (MonoidalCategory.U M) os ℓa)
  (Rg : GradedSubCat Rates.monoidalCategory M qs)
  (Ix : Set) (κ : Ix → ℕ) where

open MonoidalCategory M
open QEvaluation qro
open GradedSubCat Rg

open Families Rg Ix κ Poly⁺ poly⁺-1 (λ {s} {t} → poly⁺-· {s} {t}) public

open import CategoricalCrypto.UC.Approximate.Local approx Ix κ public

------------------------------------------------------------------------
-- The observation

private
  Sched = pointwise ℕ ℚ-ordered
  module RS = Evaluationᴹ Sched

-- The quantitative readout over SCHEDULE errors, coarsened along the
-- negligible collapse.
QEvaluationᴺ : RS.QEvaluation Fam os ℓa
QEvaluationᴺ = record
  { J = Δ J ; Ω = Δ Ω ; X = familySpace
  ; eval₀ = record
      { to = λ u i → read ⌊ hom u i ⌋ ; cong = λ eq i → read-resp₀ (eq i) }
  }

Evaluationᴺ : Evaluation Fam os ℓa
Evaluationᴺ =
  RS.qualBy QEvaluationᴺ ∼ᴺ-isEquivalence λ h → (λ _ → 0ℚ) , Negligible-0 , h

-- Its emulation order is `Abstract2`'s at `ucSetupᴺ` below.
module Canonicalᴺ = Std2.StdUC Famᴹ (Evaluation.ℰᴼ Evaluationᴺ)

open Canonicalᴺ public using () renaming (_≈ᵁ_ to _≈ℰᴺ_)

private module Rᴺ = Evaluation Evaluationᴺ

------------------------------------------------------------------------
-- A concrete bound

infix 4 _≈ℰ[_]_

-- The shape a concrete security theorem has: at every ancilla context, the
-- level-`i` advantage is at most `ε` of the security parameter and of the
-- allowance the context affords — any polynomial rate certified for its test,
-- scaled by the rate its closure carries.  This is the only place a resource
-- bound earns its keep: an uncertified context would make `ε` a function of
-- nothing, and negligibility would have no polynomial to close over.  The
-- test's rate is quantified rather than read off its own schedule, so the bound
-- is read at any certificate the test has.
_≈ℰ[_]_ : {A B : Obj^ω} → A ⇒^ω B → (ℕ → ℕ → ℚ) → A ⇒^ω B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
_≈ℰ[_]_ {A} {B} f ε g =
  (Y : Obj^ω) (Et : Rᴺ.Test (Y ⊛ω B)) (m : Rᴺ.Closure (Y ⊛ω A)) {pc : ℕ → ℕ⁺} → Poly⁺ pc
  → ((i : Ix) → Image forget (pc (κ i)) ⌊ hom Et i ⌋) → (i : Ix)
  → Rᴺ.observe (Et Canonicalᴺ.∘ Canonicalᴺ.id Canonicalᴺ.⊗₁ f) m i
      ≈[ ε (κ i) (value (pc (κ i) · schedOf m (κ i))) ]
    Rᴺ.observe (Et Canonicalᴺ.∘ Canonicalᴺ.id Canonicalᴺ.⊗₁ g) m i

-- `_≈ℰᴺ_` plugs a process into a test behind the prefix `α⇐ ∘ id ⊗₁ w`, and
-- `_≈ℰ[_]_` into the same test at `Et ∘ α⇐`: one reassociation apart.
module Reassoc {A B X Y : Obj^ω} (Et : Rᴺ.Test ((Y ⊛ω X) ⊛ω B)) (m : Rᴺ.Closure (Y ⊛ω A)) where

  plugα plugᵁ : A ⇒^ω (X ⊛ω B) → Rᴺ.Closure Rᴺ.Ω
  plugα w = ((Et Canonicalᴺ.∘ Canonicalᴺ.α⇐ {Y} {X} {B}) Canonicalᴺ.∘ Canonicalᴺ.id Canonicalᴺ.⊗₁ w) Canonicalᴺ.∘ m
  plugᵁ w = (Et Canonicalᴺ.∘ Canonicalᴺ.α⇐ {Y} {X} {B} Canonicalᴺ.∘ Canonicalᴺ.id Canonicalᴺ.⊗₁ w) Canonicalᴺ.∘ m

  reassoc : {f g : A ⇒^ω (X ⊛ω B)} → Rᴺ.read (plugα f) Rᴺ.S.≈ Rᴺ.read (plugα g)
          → Rᴺ.read (plugᵁ f) Rᴺ.S.≈ Rᴺ.read (plugᵁ g)
  reassoc {f} {g} = Rᴺ.read-cast {plugα f} {plugᵁ f} {plugα g} {plugᵁ g}
                                 (λ _ → ∘-resp-≈ˡ assoc) (λ _ → ∘-resp-≈ˡ assoc)

-- A bound held to `Negligible`, read at exactly the allowances `_≈ℰ[_]_`
-- evaluates `ε` on: a polynomial rate of the test scaled by the closure's.
CarriedNegligible : (ℕ → ℕ → ℚ) → Set (o ⊔ ℓ ⊔ e ⊔ qs)
CarriedNegligible ε = {A B : Obj^ω} (Y : Obj^ω) (Et : Rᴺ.Test (Y ⊛ω B))
                      (m : Rᴺ.Closure (Y ⊛ω A)) {pc : ℕ → ℕ⁺} → Poly⁺ pc
                    → ((i : Ix) → Image forget (pc (κ i)) ⌊ hom Et i ⌋)
                    → Negligible (λ n → ε n (value (pc n · schedOf m n)))

-- …and it is no extra assumption: `poly⁺-·` is the polynomial witness.
carried-negligible : {ε : ℕ → ℕ → ℚ} → NegligibleBound ε → CarriedNegligible ε
carried-negligible neg Y Et m {pc} Ppc _ =
  neg (λ n → value (pc n · schedOf m n)) (poly⁺-· {pc} {schedOf m} Ppc (schedOf-adm m))

infix 4 _≈ℰⁿ_

-- A bound at a negligible `ε`, with the witness KEPT, so a property whose slack
-- must stay negligible survives it.
_≈ℰⁿ_ : {A B : Obj^ω} → A ⇒^ω B → A ⇒^ω B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
f ≈ℰⁿ g = Σ[ ε ∈ (ℕ → ℕ → ℚ) ] CarriedNegligible ε × f ≈ℰ[ ε ] g

------------------------------------------------------------------------
-- The one-way bridge

-- The homs are EXPLICIT for a measured reason: both relations read them under
-- an application, so no value of one determines them by unification, and left
-- to inference the polynomial each carries is elaborated as a meta — 2m25 s of
-- `Poly` arithmetic against 8 s.  The test's rate schedule is explicit for
-- the same reason.
≈ℰⁿ⇒≈ℰᴺ : {A B X : Obj^ω} (f g : A ⇒^ω (X ⊛ω B)) → f ≈ℰⁿ g → f ≈ℰᴺ g
≈ℰⁿ⇒≈ℰᴺ {A} {B} {X} f g (ε , neg , bnd) Y = Canonicalᴺ.KE.mk∼ λ {Et} m →
  let Et′ = Et Canonicalᴺ.∘ Canonicalᴺ.α⇐ {Y} {X}
      Pc  = schedOf-adm Et′ ; c = λ i → hom Et′ i , MonoidalCategory.Equiv.refl M
  in Reassoc.reassoc {A} {B} {X} {Y} Et m {f} {g}
       ( (λ n → ε n (value (schedOf Et′ n · schedOf m n)))
       , neg Y Et′ m {schedOf Et′} Pc c
       , bnd Y Et′ m {schedOf Et′} Pc c )

------------------------------------------------------------------------
-- The canonical setup

ucSetupᴺ : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (ℓ ⊔ qs) (ℓ ⊔ qs ⊔ ℓa)
ucSetupᴺ = Canonicalᴺ.StdSetup
