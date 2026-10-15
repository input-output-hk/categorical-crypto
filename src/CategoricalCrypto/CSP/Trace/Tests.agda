{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Trace.Tests where

open import Data.Bool.Base
open import Data.Bool.Properties using (_≟_)
open import Data.List.Base
open import Data.Product.Base
open import Function.Bundles using (Func)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

import CategoricalCrypto.CSP.ObservationTests as Native
import CategoricalCrypto.CSP.Security as SourceSecurity
import CategoricalCrypto.CSP.SecurityNetwork as Networks
import CategoricalCrypto.CSP.Tests as Kernel
import CategoricalCrypto.CSP.Observation as Observation
import CategoricalCrypto.CSP.Testing as Testing
import CategoricalCrypto.CSP.Trace.Morphism as Morphism
import CategoricalCrypto.CSP.Trace.Observation as TraceObservation
import CategoricalCrypto.CSP.Trace.Security as Security
import CategoricalCrypto.CSP.Trace.Setup as Setup
import CategoricalCrypto.CSP.Trace.Testing as TraceTesting
open import CategoricalCrypto.UC.Core using (Evaluation)
open import CategoricalCrypto.UCSetup.Morphism using (UCSetupMorphism)

module Refusal where
  open Observation Bool Kernel.payload
  open TraceObservation Bool Kernel.payload
  module Full = Testing Bool Kernel.payload _≟_ Kernel.out
  module Trace = TraceTesting Bool Kernel.payload _≟_ Kernel.out

  ready-choice-traces : trace-observations Native.ready-network ≈ᵀ trace-observations Native.choice-network
  ready-choice-traces = record { traces = Native.identical-traces }

  ready-choice-evaluation : Evaluation.read Trace.evaluationᵀ Native.ready-network
    ≈ᵀ Evaluation.read Trace.evaluationᵀ Native.choice-network
  ready-choice-evaluation = ready-choice-traces

  choice-refuses : NativeObservation.failures
    (Evaluation.read Full.evaluationᶜˢᵖ Native.choice-network) [] Native.refuse-offer
  choice-refuses = Native.choice-refusal

  ready-does-not-refuse : ¬ (NativeObservation.failures
    (Evaluation.read Full.evaluationᶜˢᵖ Native.ready-network) [] Native.refuse-offer)
  ready-does-not-refuse = Native.ready-not-refusal

  raw-evaluations-differ : ¬ (Evaluation.read Full.evaluationᶜˢᵖ Native.ready-network
    ≈ᴼ Evaluation.read Full.evaluationᶜˢᵖ Native.choice-network)
  raw-evaluations-differ eq = ready-does-not-refuse (proj₂ (_≈ᴼ_.failures eq [] Native.refuse-offer) choice-refuses)

  projection-loses-refusal :
    (project (Evaluation.read Full.evaluationᶜˢᵖ Native.ready-network)
      ≈ᵀ project (Evaluation.read Full.evaluationᶜˢᵖ Native.choice-network))
    × ¬ (Evaluation.read Full.evaluationᶜˢᵖ Native.ready-network
      ≈ᴼ Evaluation.read Full.evaluationᶜˢᵖ Native.choice-network)
  projection-loses-refusal = ready-choice-evaluation , raw-evaluations-differ

module SecurityTransfer where
  open Networks
  open Morphism Bool Payload _≟_ Ω
  open TraceObservation Bool Payload
  module UC = Setup Bool Payload _≟_ Ω
  module Map = UCSetupMorphism fullCSP→traceCSP

  representatives-unchanged : ∀ {A} (t : FTest.Test A) → Func.to (Map.ν.η A) t ≡ t
  representatives-unchanged t = refl

  contextual-transfer : real-experiment TTest.≋ ideal-experiment
  contextual-transfer = consumer-cong SourceSecurity.contextual-experiments

  ordinary-transfer : real-experiment UC.≈ℰ ideal-experiment
  ordinary-transfer = ≈ℰ-preserved {f = real-experiment} {g = ideal-experiment}
    (Full.≈C⇒≈ℰ {f = real-experiment} {g = ideal-experiment} SourceSecurity.experiments-flatten)

  order-transfer : UC._≤UC_ {A = UC.ℐ.unit} {X = X} {B = B} {Y = Y} f g
  order-transfer = Security.f≤UCg

  simulator-unchanged : ∀ {X′} (a : UC.ℐ._⇒_ X X′)
    → proj₁ (Security.f≤UCg-same-simulator a) ≡ UC.ℐ._∘_ a h
  simulator-unchanged = Security.concrete-simulator

  executed-verdict : Evaluation.read TTest.evaluationᵀ ideal-experiment verdict-trace
  executed-verdict = proj₁ (_≈ᵀ_.traces Security.experiment-traces verdict-trace) Security.real-verdict
