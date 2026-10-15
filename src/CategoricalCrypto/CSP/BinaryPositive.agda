{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.CSP.BinaryPositive where

open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
import Data.Unit.Polymorphic.Base as Unit
open import Function.Bundles
open import Relation.Binary.PropositionalEquality

import CategoricalCrypto.Channel.Core as C
open import CategoricalCrypto.CSP.BinaryPresented
open import CategoricalCrypto.CSP.BinaryPresentedSource
open import CategoricalCrypto.CSP.BinaryScheduledTests using (context; context-channel; context-presentation)
import CategoricalCrypto.Machine.Relational.Presentation.Positive as Positive
open import ProbabilisticLogic.Dp.Positive

module Target = Positive.Target

positive-sender : Positive.Proc S.scheduler S.protocol
positive-sender = Positive.toPositive sender-presentation

positive-receiver : Positive.Proc S.protocol S.result
positive-receiver = Positive.toPositive receiver-presentation

positive-context : Positive.Proc S.result context-channel
positive-context = Positive.toPositive context-presentation

sender-initial : Positive (Target.point (Target.state positive-sender) Unit.tt) SendState.ready
sender-initial = Equivalence.from (Positive.initial-agreement sender-presentation SendState.ready) refl

receiver-initial : Positive (Target.point (Target.state positive-receiver) Unit.tt) ReceiveState.ready
receiver-initial = Equivalence.from (Positive.initial-agreement receiver-presentation ReceiveState.ready) refl

sender-positive-to-native : ∀ {s s′ i o}
  → Positive (Target.step positive-sender (s , i)) (s′ , o)
  → S.Sender (decode-send s) (Positive.machine-input {S.scheduler} {S.protocol} i)
      (just (Positive.machine-output {S.scheduler} {S.protocol} o)) (decode-send s′)
sender-positive-to-native {s} {s′} {i} {o} path = send-to
  (Equivalence.to (Positive.step-agreement sender-presentation s s′ i o) path)

sender-native-to-positive : ∀ {s i o t}
  → S.Sender (decode-send s) (Positive.machine-input {S.scheduler} {S.protocol} i)
      (just (Positive.machine-output {S.scheduler} {S.protocol} o)) t
  → ∃ λ s′ → Positive (Target.step positive-sender (s , i)) (s′ , o) × decode-send s′ ≡ t
sender-native-to-positive {s} {i} {o} step =
  let s′ , reflected , eq = send-from step
  in s′ , Equivalence.from (Positive.step-agreement sender-presentation s s′ i o) reflected , eq

receiver-positive-to-native : ∀ {s s′ i o}
  → Positive (Target.step positive-receiver (s , i)) (s′ , o)
  → S.Receiver (decode-receive s) (Positive.machine-input {S.protocol} {S.result} i)
      (just (Positive.machine-output {S.protocol} {S.result} o)) (decode-receive s′)
receiver-positive-to-native {s} {s′} {i} {o} path = receive-to
  (Equivalence.to (Positive.step-agreement receiver-presentation s s′ i o) path)

receiver-native-to-positive : ∀ {s i o t}
  → S.Receiver (decode-receive s) (Positive.machine-input {S.protocol} {S.result} i)
      (just (Positive.machine-output {S.protocol} {S.result} o)) t
  → ∃ λ s′ → Positive (Target.step positive-receiver (s , i)) (s′ , o) × decode-receive s′ ≡ t
receiver-native-to-positive {s} {i} {o} step =
  let s′ , reflected , eq = receive-from step
  in s′ , Equivalence.from (Positive.step-agreement receiver-presentation s s′ i o) reflected , eq

opaque
  unfolding C._⊗₀_ C.construct-⊗ Positive.machine-input Positive.machine-output

  positive-false-offer : Positive (Target.step positive-sender (SendState.ready , inj₁ S.sync))
    (SendState.returned , inj₂ (S.offer (tt , false)))
  positive-false-offer = Equivalence.from (Positive.step-agreement sender-presentation _ _ _ _) choose-false

  positive-true-offer : Positive (Target.step positive-sender (SendState.ready , inj₁ S.sync))
    (SendState.returned , inj₂ (S.offer (tt , true)))
  positive-true-offer = Equivalence.from (Positive.step-agreement sender-presentation _ _ _ _) choose-true

  positive-false-receive : Positive (Target.step positive-receiver (ReceiveState.ready , inj₁ (S.offer (tt , false))))
    (ReceiveState.returned , inj₂ S.τ)
  positive-false-receive = Equivalence.from (Positive.step-agreement receiver-presentation _ _ _ _) false-branch

  positive-true-receive : Positive (Target.step positive-receiver (ReceiveState.ready , inj₁ (S.offer (tt , true))))
    (ReceiveState.looping , inj₂ S.τ)
  positive-true-receive = Equivalence.from (Positive.step-agreement receiver-presentation _ _ _ _) true-branch
