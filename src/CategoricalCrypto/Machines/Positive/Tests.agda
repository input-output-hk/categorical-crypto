{-# OPTIONS --safe --without-K --guardedness #-}

-- Public consumers of the actual quotient category and forgetful functor.
-- The controls distinguish probability erasure from an equivalence, and
-- initializer support from a selected initial point.
module CategoricalCrypto.Machines.Positive.Tests where

open import Categories.Category.Monoidal.Bundle
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)
open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base
import Data.Rational as ℚ
open import Data.Unit.Base using (⊤; tt)
import Data.Unit.Polymorphic.Base as Unit
open import Level
open import Relation.Nullary.Negation using (¬_)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Monad
import ProbabilisticLogic.Dp.Positive.Examples as Coins
open import CategoricalCrypto.Iface
import CategoricalCrypto.UC.Machine as UC
import CategoricalCrypto.UC.Model.Seal as Seal
import CategoricalCrypto.UC.Model.Observation as Observation
import CategoricalCrypto.UC.Machine.StateEvent.HitTests as Hit
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Setup as Setup
import CategoricalCrypto.Machines.Positive.Pointwise as Point
import CategoricalCrypto.Machines.Positive.Repack as Re

private
  module R = Re.At 0ℓ
  module T = MonoidalCategory Model.𝔾₊
  module F = StrongMonoidalFunctor Model.forget-probabilities
  module FF = Functor F.F

-- This is the real non-injective hidden-state erasure from HitTests, not an
-- isomorphism or a surrogate relation on machine representatives.
ghost-forgotten : FF.F₁ (Seal.procᵒ Hit.ghost) T.≈ FF.F₁ (Seal.procᵒ Hit.erased)
ghost-forgotten = FF.F-resp-≈ (Seal.≈ᴹ⇒≈ᵒ (R.PS.≲⇒≈ᴹ Hit.erase))

biased : Dₚ Bool → R.P.Machine (⊥ ⊎ ⊤) (⊥ ⊎ Bool)
biased d = R.P.mk (record { obj = Bool ; point = λ _ → d }) λ where
  (_ , inj₁ ())
  (b , inj₂ _) → returnₚ (b , inj₂ b)

half quarter zero-weight : Seal.ifaceᵒ unitᴵ T.⇒ Seal.ifaceᵒ UC.Ωᴵ
half = Model.pack-positive (R.repack (biased Coins.half))
quarter = Model.pack-positive (R.repack (biased Coins.quarter))
zero-weight = Model.pack-positive (R.repack (biased Coins.zero-branch))

weight-erasure : half T.≈ quarter
weight-erasure = Model.pack-positive-resp (R.QS.≲⇒≈ᴹ (Point.simFn (λ b → b)
  (λ _ → ≈₊-trans (≈ₚ⇒≈₊ (>>=ₚ-identityʳ Coins.half)) Coins.half≈quarter)
  λ where
    (_ , inj₁ ())
    (b , inj₂ _) → ≈ₚ⇒≈₊ (>>=ₚ-identityʳ (returnₚ (b , inj₂ b)))))

forgetful-coins : FF.F₁ (Seal.procᵒ (biased Coins.half)) T.≈
                   FF.F₁ (Seal.procᵒ (biased Coins.quarter))
forgetful-coins = weight-erasure

both-initial-states : (b : Bool)
  → Positive (R.Q.point (R.Q.state (R.repack (biased Coins.half))) Unit.tt) b
both-initial-states = Coins.half-support

readout : (d : Dₚ Bool) → UC.⟦ biased d ⟧ᴼ ≈ₚ d
readout d = bindᶠ (λ b → >>=ₚ-identityˡ (b , inj₂ b) _) ⟨≈⟩ >>=ₚ-identityʳ d

-- The original qualitative observation (all positive rational slacks) still
-- separates the coins.  No reflection/UC equivalence is being asserted.
original-observation-separates :
  ¬ (∀ ε → ℚ._<_ ℚ.0ℚ ε → UC.⟦ biased Coins.half ⟧ᴼ ≈ₚ[ ε ] UC.⟦ biased Coins.quarter ⟧ᴼ)
original-observation-separates eq = Coins.half≁quarter λ ε pos →
  ≈ₚ[]-resp (readout Coins.half) (readout Coins.quarter) (eq ε pos)

opaque
  unfolding Seal.procᵒ Seal.unprocᵒ

  packed-readout : (d : Dₚ Bool)
    → Observation.Obs (Model.pack-positive (R.repack (biased d))) ≈ₚ d
  packed-readout = readout

zero-versus-positive : ¬ (zero-weight T.≈ half)
zero-versus-positive eq = Coins.positive-distinguished
  (≈₊-trans (≈₊-sym (≈ₚ⇒≈₊ (packed-readout Coins.zero-branch)))
    (≈₊-trans (Setup.observation-resp eq) (≈ₚ⇒≈₊ (packed-readout Coins.half))))
