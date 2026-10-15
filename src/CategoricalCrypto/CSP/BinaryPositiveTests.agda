{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.CSP.BinaryPositiveTests where

open import Categories.Category.Core
open import Categories.Category.Monoidal.Bundle
open import Data.Bool.Base
open import Data.Product.Base
open import Level using (0ℓ)

open import CategoricalCrypto.CSP.BinaryPositive
open import CategoricalCrypto.CSP.BinaryPositiveObservation
open import CategoricalCrypto.CSP.BinaryPresented
open import CategoricalCrypto.CSP.BinaryScheduledTests
import CategoricalCrypto.Machine.Relational.Presentation.Coherence as Coherence
import CategoricalCrypto.Machine.Relational.Presentation.Positive as Positive
import CategoricalCrypto.Machines.Positive.Base as Base
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Run as Run
import CategoricalCrypto.Machines.Positive.Run.Model as ModelRun
open import ProbabilisticLogic.Distribution.Uniform using (indᵇ; indᵇ-nn)
open import ProbabilisticLogic.Dp.Positive

module G = Category (Base.𝒢₊ 0ℓ)
module Q = MonoidalCategory Model.𝔾₊

independent-positive : Positive.Proc S.scheduler S.result
independent-positive = positive-receiver G.∘ positive-sender

contextual-positive : Positive.Proc S.scheduler context-channel
contextual-positive = positive-context G.∘ independent-positive

positive-composition : Positive.toPositive component-presentation G.≈ independent-positive
positive-composition = Coherence.toPositive-compose receiver-presentation sender-presentation

positive-context-composition : Positive.toPositive contextual-presentation G.≈ contextual-positive
positive-context-composition = G.Equiv.trans
  (Coherence.toPositive-compose context-presentation component-presentation)
  (G.∘-resp-≈ G.Equiv.refl positive-composition)

quotient-composition : Positive.toQuotient component-presentation Q.≈
  (Positive.toQuotient receiver-presentation Q.∘ Positive.toQuotient sender-presentation)
quotient-composition = Coherence.toQuotient-compose receiver-presentation sender-presentation

quotient-context-composition : Positive.toQuotient contextual-presentation Q.≈
  (Positive.toQuotient context-presentation Q.∘
    (Positive.toQuotient receiver-presentation Q.∘ Positive.toQuotient sender-presentation))
quotient-context-composition = Q.Equiv.trans
  (Coherence.toQuotient-compose context-presentation component-presentation)
  (Q.∘-resp-≈ Q.Equiv.refl quotient-composition)

independently-composed-positive-test : PositiveTest (Run.run contextual-positive exchange-then-finish) (indᵇ true)
independently-composed-positive-test = proj₁ (Run.run-resp positive-context-composition exchange-then-finish)
  (indᵇ true) (indᵇ-nn true) presented-positive-test

contextual-quotient : Positive.target-interface S.scheduler Q.⇒ Positive.target-interface context-channel
contextual-quotient = Positive.toQuotient context-presentation Q.∘
  (Positive.toQuotient receiver-presentation Q.∘ Positive.toQuotient sender-presentation)

sealed-independently-composed-positive-test : PositiveTest
  (ModelRun.run {scheduler-boundary} {context-boundary} contextual-quotient exchange-then-finish) (indᵇ true)
sealed-independently-composed-positive-test = proj₁
  (ModelRun.run-resp {scheduler-boundary} {context-boundary} quotient-context-composition exchange-then-finish)
  (indᵇ true) (indᵇ-nn true) sealed-presented-positive-test
