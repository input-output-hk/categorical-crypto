{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.CSP.BinaryPositiveObservation where

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Rational.Properties.Ext using (0<1ℚ)
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Bundles
open import Relation.Binary.PropositionalEquality

import CategoricalCrypto.Channel.Core as C
open import CategoricalCrypto.CSP.BinaryPositive
open import CategoricalCrypto.CSP.BinaryPresented
open import CategoricalCrypto.CSP.BinaryScheduledTests
import CategoricalCrypto.Iface as I
open import CategoricalCrypto.Machine.Relational.Presentation
open import CategoricalCrypto.Machine.Relational.Presentation.Composition
import CategoricalCrypto.Machine.Relational.Presentation.Positive as Positive
import CategoricalCrypto.Machine.Relational.Wiring as W
import CategoricalCrypto.Machines.Positive.Run as Run
import CategoricalCrypto.Machines.Positive.Run.Model as ModelRun
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.Uniform using (indᵇ; indᵇ-nn)
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Composition
open import ProbabilisticLogic.Dp.Positive.Paths

component-presentation : Presentation finite
component-presentation = compose-presentation receiver-presentation sender-presentation

contextual-presentation : Presentation (context W.∘ finite)
contextual-presentation = compose-presentation context-presentation component-presentation

after-finish : S.Label ⊎ Acknowledgement → Strat (S.Command ⊎ ⊥) (S.Label ⊎ Acknowledgement)
after-finish (inj₁ _) = out false
after-finish (inj₂ exchange-ack) = out false
after-finish (inj₂ finished) = out true

after-exchange : S.Label ⊎ Acknowledgement → Strat (S.Command ⊎ ⊥) (S.Label ⊎ Acknowledgement)
after-exchange (inj₁ _) = out false
after-exchange (inj₂ exchange-ack) = ask (inj₁ S.finish) after-finish
after-exchange (inj₂ finished) = out false

exchange-then-finish : Strat (S.Command ⊎ ⊥) (S.Label ⊎ Acknowledgement)
exchange-then-finish = ask (inj₁ S.sync) after-exchange

test-asks-at-most-two : asks≤ 2 exchange-then-finish
test-asks-at-most-two (inj₁ _) = tt
test-asks-at-most-two (inj₂ exchange-ack) (inj₁ _) = tt
test-asks-at-most-two (inj₂ exchange-ack) (inj₂ exchange-ack) = tt
test-asks-at-most-two (inj₂ exchange-ack) (inj₂ finished) = tt
test-asks-at-most-two (inj₂ finished) = tt

opaque
  unfolding C._⊗₀_ C.construct-⊗ Positive.machine-input Positive.machine-output

  presented-accepts : Positive (Run.run (Positive.toPositive contextual-presentation) exchange-then-finish) true
  presented-accepts = bind-path
    (Equivalence.from (Positive.initial-agreement contextual-presentation _) ((refl , refl) , refl))
    (bind-path
      (Equivalence.from (Positive.step-agreement contextual-presentation _ _ (inj₁ S.sync) (inj₂ exchange-ack)) context-exchange)
      (bind-path
        (Equivalence.from (Positive.step-agreement contextual-presentation _ _ (inj₁ S.finish) (inj₂ finished)) context-termination)
        (positive-return true)))

presented-positive-test : PositiveTest (Run.run (Positive.toPositive contextual-presentation) exchange-then-finish) (indᵇ true)
presented-positive-test = positive-witness (indᵇ true) (indᵇ-nn true) presented-accepts 0<1ℚ

scheduler-boundary context-boundary : I.Iface
scheduler-boundary = C.Channel.inType S.scheduler I.⇿ C.Channel.outType S.scheduler
context-boundary = C.Channel.inType context-channel I.⇿ C.Channel.outType context-channel

sealed-presented-positive-test : PositiveTest
  (ModelRun.run {scheduler-boundary} {context-boundary}
    (Positive.toQuotient contextual-presentation) exchange-then-finish) (indᵇ true)
sealed-presented-positive-test = proj₂
  (ModelRun.pack-run {scheduler-boundary} {context-boundary}
    (Positive.toPositive contextual-presentation) exchange-then-finish)
  (indᵇ true) (indᵇ-nn true) presented-positive-test
