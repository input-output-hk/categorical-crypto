{-# OPTIONS --safe --guardedness #-}

-- The graph of a pure simulation is a bisimulation once singleton support
-- can be tested.  No representation or cardinality condition is imposed on
-- the state and port types.
module CategoricalCrypto.Machine.Relational.Presentation.Classical where

open import Axiom.ExcludedMiddle
open import Categories.Category.Monoidal.Bundle
open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Unit.Polymorphic.Base
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Composition
open import ProbabilisticLogic.Dp.Positive.Decidability
open import ProbabilisticLogic.Dp.Positive.Monad

import CategoricalCrypto.Channel.Core as Ch
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation
open import CategoricalCrypto.Machine.Relational.Presentation.Canonical
open import CategoricalCrypto.Machine.Relational.Presentation.Descent using (channel; canonical; PMDescent; PMmayDescent)
import CategoricalCrypto.Machine.Relational.Presentation.Positive as EP
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.Machines.Positive.Run as Run
import CategoricalCrypto.UC.Model.Seal as Seal

private
  module R = Re.At 0ℓ
  variable
    A B : Ch.Channel
    X : Set
    d e : Dₚ X
    x : X

module WithLEM (lem : ExcludedMiddle 0ℓ) where
  equality : {X : Set} → DecidableEquality X
  equality x y = lem

  positive-support : d ≈₊ e → Positive d x → Positive e x
  positive-support {x = x} = decidable-positive-support equality x

  literal-support : d ≈ₚ e → Positive d x → Positive e x
  literal-support {x = x} = decidable-literal-support equality x

  opaque
    unfolding Ch._⊗₀_

    compile-step : (f : EP.Proc A B) → Stepₚ A B (R.Q.St f)
    compile-step f s i = R.Q.step f (s , i)

  compile : EP.Proc A B → Initialized A B
  compile f = fromₚ (R.Q.point (R.Q.state f) tt) (compile-step f)

  opaque
    unfolding Ch._⊗₀_ compile-step

    simulation : {f g : EP.Proc A B} → f R.QS.≲ g → compile f ≈ᴿ compile g
    simulation {f = f} {g} sim = record
      { Related = λ s t → Run.ϕ sim s ≡ t
      ; initial-to = λ p → _ , positive-support (Run.point-sim sim) (map-path (Run.ϕ sim) p) , refl
      ; initial-from = λ p → map-unpath (Run.ϕ sim) (positive-support (≈₊-sym (Run.point-sim sim)) p)
      ; step-to = λ
          { {o = just o} refl p → _ , positive-support (Run.step-sim sim _) (map-path (λ r → Run.ϕ sim (proj₁ r) , proj₂ r) p) , refl
          ; {o = nothing} refl () }
      ; step-from = λ
          { {s = s} {i = i} {o = just o} refl p →
              let (s′ , o′) , path , eq = map-unpath (λ r → Run.ϕ sim (proj₁ r) , proj₂ r)
                    (positive-support (≈₊-sym (Run.step-sim sim (s , i))) p)
              in s′ , subst (λ o → Positive (R.Q.step f (s , i)) (s′ , o)) (cong proj₂ eq) path , cong proj₁ eq
          ; {o = nothing} refl () }
      }

  congruence : {f g : EP.Proc A B} → f R.QS.≈ᴹ g → compile f ≈ᴿ compile g
  congruence = EqC.fold (record { refl = ≈ᴿ-refl ; sym = ≈ᴿ-sym ; trans = ≈ᴿ-trans }) simulation

  opaque
    unfolding Ch._⊗₀_ compile-step EP.positive-step

    presentation : {F : Initialized A B} (P : Presentation F) → compile (EP.toPositive P) ≈ᴿ F
    presentation P = record
      { Related = _≡_
      ; initial-to = λ p → _ , initial-sound P p , refl
      ; initial-from = λ p → _ , initial-complete P p , refl
      ; step-to = λ { {o = just o} refl p → _ , step-sound P p , refl
                    ; {o = nothing} refl () }
      ; step-from = λ { {o = just o} refl p → _ , step-complete P p , refl
                      ; {o = nothing} refl p → ⊥-elim (no-refusal P p) }
      }

  opaque
    unfolding Ch._⊗₀_ compile-step canonical Seal.𝔾ᵒ Seal.procᵒ Seal.ifaceᵒ
              Model.positive-congruence Model._≈⁺_

    pmmay-descent : PMmayDescent
    pmmay-descent eq = congruence eq

    pm-descent : PMDescent
    pm-descent eq = congruence (R.repack-resp eq)
