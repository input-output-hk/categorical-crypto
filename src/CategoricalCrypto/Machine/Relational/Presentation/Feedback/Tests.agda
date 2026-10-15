{-# OPTIONS --safe --guardedness #-}

-- A genuine stateful feedback experiment: one branch answers immediately;
-- the other sends a hidden-port message, changes state, re-enters, and only
-- then answers false.  Both are finite positive observations, not FD claims.
module CategoricalCrypto.Machine.Relational.Presentation.Feedback.Tests where

open import Categories.Category.Monoidal.Bundle
open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (refl)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Composition
open import ProbabilisticLogic.Dp.Positive.Paths
open import ProbabilisticLogic.Dp.Positive.Monad
import ProbabilisticLogic.Dp.Positive.Loop as Loop
import ProbabilisticLogic.Dp.Positive.Examples as Coins
open import ProbabilisticLogic.Distribution.Uniform using (indᵇ; indᵇ-nn)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation
import CategoricalCrypto.Machine.Relational.Presentation.Canonical as Canonical
import CategoricalCrypto.Machine.Relational.Presentation.Trace as Trace
import CategoricalCrypto.Machine.Relational.Presentation.Positive as EP
import CategoricalCrypto.Machine.Relational.Presentation.Feedback as Native
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.Machines.Positive.Run as Run
import CategoricalCrypto.Machines.Positive.Run.Model as PublicRun
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Feedback.Model as Feedback
import CategoricalCrypto.Iface as I
import CategoricalCrypto.UC.Model.Seal as Seal
open import CategoricalCrypto.Strategy

private
  module R = Re.At 0ℓ
  module T = MonoidalCategory Model.𝔾₊

silent verdict hidden : Channel
silent = ⊥ ⇿ ⊥
verdict = Bool ⇿ ⊤
hidden = ⊤ ⇿ ⊤

private
  FI FO EO : Set
  FI = (⊥ ⊎ ⊤) ⊎ (⊤ ⊎ ⊤)
  FO = (⊥ ⊎ ⊤) ⊎ (Bool ⊎ ⊤)
  EO = ⊥ ⊎ Bool

branch : Bool → Bool × FO
branch true = false , inj₂ (inj₁ true)
branch false = true , inj₂ (inj₂ tt)

opaque
  unfolding _⊗₀_

  kernel : Canonical.Stepₚ (silent ⊗₀ hidden) (verdict ⊗₀ hidden) Bool
  kernel _ (inj₁ (inj₁ ()))
  kernel false (inj₁ (inj₂ _)) = botₚ
  kernel true (inj₁ (inj₂ _)) = returnₚ (false , inj₂ (inj₁ false))
  kernel false (inj₂ (inj₁ _)) = mapₚ branch Coins.half
  kernel true (inj₂ (inj₁ _)) = botₚ
  kernel _ (inj₂ (inj₂ _)) = botₚ

represented : Initialized (silent ⊗₀ hidden) (verdict ⊗₀ hidden)
represented = Canonical.fromₚ {A = silent ⊗₀ hidden} {B = verdict ⊗₀ hidden} (returnₚ false) kernel

relay : Presentation represented
relay = Canonical.presentₚ {A = silent ⊗₀ hidden} {B = verdict ⊗₀ hidden} (returnₚ false) kernel

private
  loop = Trace.trace-presentation {A = silent} {C = hidden} {B = verdict} relay
  loop-machine = EP.toPositive loop

opaque
  unfolding _⊗₀_

  U : Body Bool FI EO
  U = Trace.body relay

opaque
  unfolding _⊗₀_ kernel Trace.body Trace.dispatch U

  immediate : Loop.Run U (U (false , inj₂ (inj₁ tt))) (false , inj₂ true)
  immediate = Loop.finish
    (map-path (Trace.dispatch relay) (map-path branch (Coins.half-support true))) refl

  reentry : Loop.Run U (U (false , inj₂ (inj₁ tt))) (false , inj₂ false)
  reentry = Loop.again
    (map-path (Trace.dispatch relay) (map-path branch (Coins.half-support false)))
    (Loop.finish (map-path (Trace.dispatch relay) (positive-return (false , inj₂ (inj₁ false)))) refl)

observe : Strat (⊥ ⊎ ⊤) (⊥ ⊎ Bool)
observe = ask (inj₂ tt) λ where
  (inj₁ ())
  (inj₂ b) → out b

opaque
  unfolding _⊗₀_ EP.positive-step Trace.trace-presentation Trace.input U

  step-path : (b : Bool) → Positive (R.Q.step loop-machine (false , inj₂ tt)) (false , inj₂ b)
  step-path true = Loop.to-positive immediate
  step-path false = Loop.to-positive reentry

  run-path : (b : Bool) → Positive (Run.run loop-machine observe) b
  run-path b = bind-path (positive-return false) (bind-path (step-path b) (positive-return b))

private
  Ωᴵ = Bool I.⇿ ⊤
  Xᴵ = ⊤ I.⇿ ⊤

feedback : Seal.ifaceᵒ I.unitᴵ T.⇒ Seal.ifaceᵒ Ωᴵ
feedback = Feedback.feedback {I.unitᴵ} {Xᴵ} {Ωᴵ}
  (Model.pack-positive {I.unitᴵ I.⊗ᴵ Xᴵ} {Ωᴵ I.⊗ᴵ Xᴵ} (Native.tensor-positive relay))

private
  self-positive : ∀ b → 0ℚ ℚ.< indᵇ b b
  self-positive true = 0<1ℚ
  self-positive false = 0<1ℚ

-- These conclusions use the ACTUAL public target feedback and its checked
-- quotient-stable finite experiment runner.
feedback-may : (b : Bool) → PositiveTest (PublicRun.run feedback observe) (indᵇ b)
feedback-may b = proj₁
  (≈₊-trans (≈₊-sym (PublicRun.pack-run loop-machine observe))
    (PublicRun.run-resp (Native.toQuotient-trace relay) observe))
  (indᵇ b) (indᵇ-nn b) (positive-witness (indᵇ b) (indᵇ-nn b) (run-path b) (self-positive b))
