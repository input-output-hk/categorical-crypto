{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.ClassicalConsumers where

open import Axiom.ExcludedMiddle
open import Categories.Category.Monoidal.Bundle
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)
open import Data.Bool.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Function.Bundles
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary.Negation using (¬_)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Composition
import ProbabilisticLogic.Dp.Positive.Examples as Coins

import CategoricalCrypto.Channel.Core as Ch
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation
open import CategoricalCrypto.Machine.Relational.Presentation.Descent using (canonical)
import CategoricalCrypto.Machine.Relational.Observation as Observation
import CategoricalCrypto.Machine.Relational.Setup as Native
import CategoricalCrypto.Machine.Relational.Wiring as W
import CategoricalCrypto.Machine.Relational.Presentation.Classical as Classical
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalMonoidal as Monoidal
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalObservation as Readout
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalSetup as Setup
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalFeedback as Feedback
import CategoricalCrypto.Machine.Relational.Presentation.Feedback as TraceComparison
import CategoricalCrypto.Machine.Relational.Presentation.Feedback.Tests as Relay
import CategoricalCrypto.Machine.Relational.Presentation.Positive as EP
import CategoricalCrypto.Machine.Relational.Presentation.Trace as Trace
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.Machines.Positive.Tests as Source
import CategoricalCrypto.UC.Machine.StateEvent.HitTests as Hit
import CategoricalCrypto.UC.Model.Seal as Seal
import CategoricalCrypto.UC.Model.Setup as PM
import CategoricalCrypto.Abstract2.Morphism as Transfer
open import CategoricalCrypto.UCSetup.Morphism

private
  module R = Re.At 0ℓ
  module Q = MonoidalCategory Model.𝔾₊

module WithLEM (lem : ExcludedMiddle 0ℓ) where
  module C = Classical.WithLEM lem
  module Read = Readout.WithLEM lem
  module Strong = Monoidal.WithLEM lem
  module Original = StrongMonoidalFunctor Strong.PM→native
  module May = StrongMonoidalFunctor Strong.PMmay→native
  module Public = Setup.WithLEM lem
  module Morphism = UCSetupMorphism Public.PM→native
  module Transport = Transfer.Transfer Public.PM→native

  ghost-erasure : Original.F₁ (Seal.procᵒ Hit.ghost) ≈ᴿ Original.F₁ (Seal.procᵒ Hit.erased)
  ghost-erasure = Original.F-resp-≈ (Seal.≈ᴹ⇒≈ᵒ (R.PS.≲⇒≈ᴹ Hit.erase))

  half-quarter : May.F₁ Source.half ≈ᴿ May.F₁ Source.quarter
  half-quarter = May.F-resp-≈ Source.weight-erasure

  opaque
    unfolding Ch._⊗₀_ canonical C.compile-step

    all-initial-states : (b : Bool) → initial (C.compile (R.repack (Source.biased Coins.half))) b
    all-initial-states = Coins.half-support

    zero-initial-excluded : ¬ initial (C.compile (R.repack (Source.biased Coins.zero-branch))) true
    zero-initial-excluded path with positive-return-reflect (C.literal-support Coins.zero-erased path)
    ... | ()

    both-verdicts : (b : Bool) → Observation.eval (canonical (Source.biased Coins.half)) b
    both-verdicts b = Read.readout-to (Source.biased Coins.half)
      (C.literal-support (≈ₚ-sym _ _ (Source.readout Coins.half)) (Coins.half-support b))

    zero-verdict-excluded : ¬ Observation.eval (canonical (Source.biased Coins.zero-branch)) true
    zero-verdict-excluded observed = zero-initial-excluded
      (C.literal-support (Source.readout Coins.zero-branch)
        (Read.readout-from (Source.biased Coins.zero-branch) observed))

  opaque
    unfolding Ch._⊗₀_ canonical C.compile-step EP.positive-step Trace.trace-presentation
              Observation.tick Observation.verdict Seal.𝔾ᵒ Seal.ifaceᵒ Seal.procᵒ Seal.unprocᵒ
              Model.positive-congruence

    feedback-canonical : canonical (Seal.unprocᵒ Relay.feedback) ≈ᴿ W.trace Relay.represented
    feedback-canonical = ≈ᴿ-trans
      (C.pmmay-descent (Q.Equiv.sym (TraceComparison.toQuotient-trace Relay.relay)))
      (≈ᴿ-trans (C.congruence (R.repack-unpack (EP.toPositive (Trace.trace-presentation Relay.relay))))
        (C.presentation (Trace.trace-presentation Relay.relay)))

    feedback-both-verdicts : (b : Bool) → Observation.eval (canonical (Seal.unprocᵒ Relay.feedback)) b
    feedback-both-verdicts b = Observation.eval-to (≈ᴿ-sym feedback-canonical)
      (false , positive-return false , false , step-sound (Trace.trace-presentation Relay.relay) (Relay.step-path b))

  -- This square uses the original public setup's simulator substitution, not
  -- an invented operation on representatives.  It needs no test-surjectivity
  -- or assertion that arbitrary native relations have PM presentations.
  simulator-square : ∀ {X Y A B} (s : X PM.⇒ Y) (f : A PM.⇒ PM.T₀ X B)
    → Transport.G (PM.sub s PM.∘ f) ≈ᴿ (Native.sub (Morphism.Φ.₁ s) Native.∘ Transport.G f)
  simulator-square s f = let open Native.𝒞.HomReasoning in
    (refl⟩∘⟨ Morphism.F.homomorphism) ○ Native.𝒞.sym-assoc
      ○ (Morphism.κ-sub s ⟩∘⟨refl) ○ Native.𝒞.assoc

  simulator-context : ∀ {X Y A B} (s : X PM.⇒ Y) (f : A PM.⇒ PM.T₀ X B)
    (test : Initialized (Native.T₀ (Morphism.Φ.₀ Y) (Morphism.F.₀ B)) Observation.Ω)
    (preparation : Initialized Observation.J (Morphism.F.₀ A)) (b : Bool)
    → Observation.eval (test W.∘ (Transport.G (PM.sub s PM.∘ f) W.∘ preparation)) b
      ⇔ Observation.eval (test W.∘ ((Native.sub (Morphism.Φ.₁ s) Native.∘ Transport.G f) W.∘ preparation)) b
  simulator-context s f test preparation = Observation.eval-resp
    (W.∘-cong ≈ᴿ-refl (W.∘-cong (simulator-square s f) ≈ᴿ-refl))
