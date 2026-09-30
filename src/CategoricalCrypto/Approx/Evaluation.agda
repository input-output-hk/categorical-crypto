{-# OPTIONS --safe --without-K #-}

-- The quantitative readout, and the qualitative readouts it induces.
--
-- `eval₀` lands in an APPROXIMATE space and observes the ambient hom equality
-- EXACTLY — that is what `zeroSetoid` says, and what makes precomposition
-- nonexpansive downstream (`UC.Quantitative.Observed`).  Forgetting the error
-- leaves the reading itself untouched and only coarsens its equality, which is
-- what `qualBy` takes: any equivalence that zero error already implies.
-- `qual` is the exact one and `qual₊` closeness at every positive error of a
-- `Refinement`; a tier that KEEPS an error witness coarsens by its own class
-- instead (`UC.Family.Negligible.Evaluationᴺ`).

open import Categories.Category.Core using (Category)

open import Function.Base using (_∘′_)
open import Function.Bundles using (Func)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)

open import CategoricalCrypto.Approx.Error using (module AllPositive; OrderedErrorAlgebra; Refinement)
open import CategoricalCrypto.UC.Core using (Evaluation)

module CategoricalCrypto.Approx.Evaluation
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E using (ε₀)
open import CategoricalCrypto.Approx.Space E

private variable
  o ℓ e cs ℓa ℓt : Level
  𝒞 : Category o ℓ e

record QEvaluation (𝒞 : Category o ℓ e) (cs ℓa : Level)
              : Set (o ⊔ ℓ ⊔ e ⊔ es ⊔ ℓe ⊔ suc cs ⊔ suc ℓa) where
  open Category 𝒞

  field
    J Ω   : Obj
    X     : ApproxSpace cs ℓa
    eval₀ : Func (hom-setoid {J} {Ω}) (zeroSetoid X)

  open ApproxSpace X public

  read : J ⇒ Ω → Carrier
  read = Func.to eval₀

  read-resp₀ : {u v : J ⇒ Ω} → u ≈ v → read u ≈[ ε₀ ] read v
  read-resp₀ = Func.cong eval₀

qualBy : (Q : QEvaluation 𝒞 cs ℓa) {_∼_ : Rel (QEvaluation.Carrier Q) ℓt}
       → IsEquivalence _∼_
       → ({x y : QEvaluation.Carrier Q} → QEvaluation._≈[_]_ Q x ε₀ y → x ∼ y)
       → Evaluation 𝒞 cs ℓt
qualBy Q {_∼_} eqv coarsen = record
  { J = J ; Ω = Ω
  ; S = record { Carrier = Carrier ; _≈_ = _∼_ ; isEquivalence = eqv }
  ; eval = record { to = read ; cong = coarsen ∘′ read-resp₀ }
  }
  where open QEvaluation Q

qual : (Q : QEvaluation 𝒞 cs ℓa) → Evaluation 𝒞 cs ℓa
qual Q = qualBy Q (Setoid.isEquivalence (zeroSetoid (QEvaluation.X Q))) λ h → h

qual₊ : Refinement E → (Q : QEvaluation 𝒞 cs ℓa) → Evaluation 𝒞 cs (es ⊔ ℓe ⊔ ℓa)
qual₊ R Q = qualBy Q ∼ᵃ-isEquivalence zero⇒positive
  where open AllPositive R (QEvaluation.approx Q)
