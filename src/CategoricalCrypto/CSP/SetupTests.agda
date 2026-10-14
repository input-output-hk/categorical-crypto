{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.SetupTests where

open import Categories.Category.Core
open import Data.Bool.Base
open import Data.Bool.Properties using (_≟_)
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base using (just)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes)

import CategoricalCrypto.CSP.GlobalClasses as Global
import CategoricalCrypto.CSP.Monoidal as Monoidal
import CategoricalCrypto.CSP.NativeTests as Native
import CategoricalCrypto.CSP.ObservationTests as Discriminators
import CategoricalCrypto.CSP.Security as Security
import CategoricalCrypto.CSP.SecurityNetwork as Example
import CategoricalCrypto.CSP.Setup as Setup
import CategoricalCrypto.CSP.Tests as Kernel
import CategoricalCrypto.CSP.Interface as Interfaces
import CategoricalCrypto.CSP.Observation as Observations
import CategoricalCrypto.CSP.Plugging as Plugging
open import CategoricalCrypto.CSP.Category Bool Example.Payload
open import CategoricalCrypto.CSP.Interface Bool Example.Payload
open import CategoricalCrypto.CSP.Network Bool Example.Payload
open import CategoricalCrypto.CSP.Observation Bool Example.Payload
open import CategoricalCrypto.CSP.Operational Bool Example.Payload
open import CategoricalCrypto.CSP.Plugging Bool Example.Payload
open import CategoricalCrypto.CSP.Separation Bool Example.Payload
import CategoricalCrypto.CSP.Testing as Testing
open import CategoricalCrypto.UC.Core using (Evaluation)
open import CategoricalCrypto.UCSetup using (UCSetup)

module Verdict = Testing Bool Example.Payload _≟_ Example.Ω
module Protocol = Setup Bool Example.Payload _≟_ Example.Ω
module TensorVerdict = Testing Bool Example.Payload _≟_ (Example.Ω ⊗₀ Example.Ω)
module KI = Interfaces Bool Kernel.payload
module KPlug = Plugging Bool Kernel.payload
module KObs = Observations Bool Kernel.payload
module GI = Interfaces Bool Global.payload
module GObs = Observations Bool Global.payload
module UnitVerdict = Testing Bool Kernel.payload _≟_ Kernel.out
module ClosedVerdict = Testing Bool Kernel.payload _≟_ KI.I
module GlobalClosed = Testing Bool Global.payload _≟_ GI.I
module GlobalVerdict = Testing Bool Global.payload _≟_ Global.out
module Cat = Category OpenCSP
module NI = Interfaces ⊤ (λ _ → ⊤)
module NObs = Observations ⊤ (λ _ → ⊤)
module NativeClosed = Testing ⊤ (λ _ → ⊤) (λ { tt tt → yes refl }) NI.I
module ReturnedBlocked = Native.PrivateUnit.ReturnedBlocked
module ReturnedSpinning = Native.PrivateUnit.Spinning
module NL = ReturnedBlocked.K.Local (inj₁ tt)
module ReturnedBlockedObs = NObs.Observe ReturnedBlocked.network
module ReturnedSpinningObs = NObs.Observe ReturnedSpinning.network

public-consumer : Verdict.Test (Example.X ⊗₀ Example.B)
public-consumer = Example.t

public-real-verdict : NativeObservation.traces
  (Evaluation.read Verdict.evaluationᶜˢᵖ Example.real-experiment) Example.verdict-trace
public-real-verdict = Example.real-verdict-trace

public-ideal-verdict : NativeObservation.traces
  (Evaluation.read Verdict.evaluationᶜˢᵖ Example.ideal-experiment) Example.verdict-trace
public-ideal-verdict = Security.ideal-verdict-trace

public-real-terminal-refusal : ∀ refusal → NativeObservation.failures
  (Evaluation.read Verdict.evaluationᶜˢᵖ Example.real-experiment) Example.verdict-trace refusal
public-real-terminal-refusal = Example.real-terminal-refusal

public-ideal-terminal-refusal : ∀ refusal → NativeObservation.failures
  (Evaluation.read Verdict.evaluationᶜˢᵖ Example.ideal-experiment) Example.verdict-trace refusal
public-ideal-terminal-refusal = Security.ideal-terminal-refusal

public-equal-triples : Evaluation.read Verdict.evaluationᶜˢᵖ Example.real-experiment
  ≈ᴼ Evaluation.read Verdict.evaluationᶜˢᵖ Example.ideal-experiment
public-equal-triples = Security.experiment-observations

public-pull-consumer : Verdict.pull Example.f public-consumer ≡ Example.real-experiment
public-pull-consumer = refl

public-contextual-equality : Example.real-experiment Verdict.≋ Example.ideal-experiment
public-contextual-equality = Security.contextual-experiments

public-setup-category : UCSetup.𝒞 Protocol.StdSetup ≡ OpenCSP
public-setup-category = refl

public-setup-grades : UCSetup.ℐ Protocol.StdSetup ≡ Monoidal.OpenCSPᴹ Bool Example.Payload
public-setup-grades = refl

public-setup-tests : UCSetup.ℰ Protocol.StdSetup ≡ Verdict.ℰᶜˢᵖ
public-setup-tests = refl

public-grade-action : ∀ X B → Protocol.T₀ X B ≡ (X ⊗₀ B)
public-grade-action X B = refl

public-grade-action-arrow : ∀ X {A B} (r : Network A B) → Protocol.T₁ X r ≡ (id {X} ⊗₁ r)
public-grade-action-arrow X r = refl

public-quantified-security : Protocol._≤UC_
  {A = I} {X = Example.X} {B = Example.B} {Y = Example.Y} Example.f Example.g
public-quantified-security = Security.f≤UCg

public-simulator-computation : ∀ {X′} (a : Network Example.X X′)
  → proj₁ (public-quantified-security a) ≡ (a ∘ Example.h)
public-simulator-computation a = refl

public-ancillary-security : ∀ {X′} (a : Network Example.X X′) W →
  Protocol._≈ℰ_
    (Protocol.μ W X′ ∘ Protocol.T₁ W ((a ⊗₁ id {Example.B}) ∘ Example.f))
    (Protocol.μ W X′ ∘ Protocol.T₁ W ((Security.simulator a ⊗₁ id {Example.B}) ∘ Example.g))
public-ancillary-security a W = proj₂ (public-quantified-security a) W

identity-has-no-boxes : Boxes.shape (Network.components (id {Example.B})) ≡ empty
identity-has-no-boxes = refl

identity-plugging-tests : (id {Example.Ω} ∘ Example.real-experiment) Verdict.≋ Example.real-experiment
identity-plugging-tests = Verdict.structural⇒test-equality Cat.identityˡ

associative-tests : ∀ {A B C} (r : Network I A) (s : Network A B) (u : Network B C) (v : Network C Example.Ω)
  → (v ∘ ((u ∘ s) ∘ r)) Verdict.≋ (v ∘ (u ∘ (s ∘ r)))
associative-tests {A} {B} {C} r s u v = Verdict.structural⇒test-equality
  {A = I} {t = v ∘ ((u ∘ s) ∘ r)} {u = v ∘ (u ∘ (s ∘ r))}
  (Cat.∘-resp-≈ʳ {A = I} {B = C} {C = Example.Ω}
    {f = (u ∘ s) ∘ r} {h = u ∘ (s ∘ r)} {g = v}
    (Cat.assoc {A = I} {B = A} {C = B} {D = C} {f = r} {g = s} {h = u}))

module AliasObs = KObs.Observe (KPlug._∘_ (KPlug.id {Kernel.out}) Kernel.producer)

transparent-alias-trace : KObs.NativeObservation.traces
  (Evaluation.read UnitVerdict.evaluationᶜˢᵖ (KPlug._∘_ (KPlug.id {Kernel.out}) Kernel.producer))
  (Kernel.Alias.event (inj₂ tt , tt) ∷ [])
transparent-alias-trace = _ , AliasObs.visible-step Kernel.transparent-visible-offer AliasObs.done

module HiddenObs = KObs.Observe Kernel.experiment

hidden-rendezvous-trace : KObs.NativeObservation.traces
  (Evaluation.read ClosedVerdict.evaluationᶜˢᵖ Kernel.experiment) (Kernel.Hidden.√ ∷ [])
hidden-rendezvous-trace = Kernel.Hidden.completed , HiddenObs.silent-step Kernel.hidden-rendezvous
  (HiddenObs.visible-step Kernel.joint-return HiddenObs.done)

module ThreeObs = GObs.Observe (Global.closed Global.receiver)

three-way-trace : GObs.NativeObservation.traces
  (Evaluation.read GlobalClosed.evaluationᶜˢᵖ (Global.closed Global.receiver)) (Global.Three.√ ∷ [])
three-way-trace = Global.Three.completed , ThreeObs.silent-step Global.three-advance-atomically
  (ThreeObs.visible-step Global.three-joint-completion ThreeObs.done)

three-way-blocked-refusal : GObs.NativeObservation.failures
  (Evaluation.read GlobalClosed.evaluationᶜˢᵖ (Global.closed Global.R.stop)) [] (λ _ → ⊤)
three-way-blocked-refusal = Global.Blocked.initial-configuration , Global.BlockedObs.done , Global.blocked-class-refuses-all

blocked-boundary-no-trace : ¬ (GObs.NativeObservation.traces
  (Evaluation.read GlobalVerdict.evaluationᶜˢᵖ (Global.exposed Global.R.stop))
  (Global.Public.event (inj₂ tt , tt) ∷ []))
blocked-boundary-no-trace (q , path) = no-path path
  where
  module O = GObs.Observe (Global.exposed Global.R.stop)
  no-silent : ∀ {q} → ¬ (Global.Public._─[_]→_ Global.Public.initial-configuration Global.Public.τ q)
  no-silent (Global.Public.internal {k = inj₁ (inj₁ tt)} step) = Global.sender-no-silent step
  no-silent (Global.Public.internal {k = inj₁ (inj₂ tt)} step) = Global.receiver-no-silent step
  no-silent (Global.Public.internal {k = inj₂ tt} step) = Global.R.stop-no-step step
  no-silent (Global.Public.hidden {n = inj₁ tt} _ _ priv _) = priv (inj₂ tt) Global.public-connection
  no-silent (Global.Public.hidden {n = inj₂ (inj₁ ())} _ _ _ _)
  no-silent (Global.Public.hidden {n = inj₂ (inj₂ tt)} _ _ priv _) = priv (inj₂ tt) Global.PublicW.same
  no-path : ∀ {q} → O.Executes Global.Public.initial-configuration
    (Global.Public.event (inj₂ tt , tt) ∷ []) q → ⊥
  no-path (O.silent-step step rest) = no-silent step
  no-path (O.visible-step step rest) = Global.public-no-visible-event step

empty-identity-no-trace : ¬ (KObs.NativeObservation.traces
  (Evaluation.read ClosedVerdict.evaluationᶜˢᵖ (KPlug.id {KI.I})) (Kernel.Empty.√ ∷ []))
empty-identity-no-trace (q , path) = no-path path
  where
  module O = KObs.Observe (KPlug.id {KI.I})
  no-path : ∀ {q} → O.Executes Kernel.Empty.initial-configuration (Kernel.Empty.√ ∷ []) q → ⊥
  no-path (O.silent-step step rest) = Kernel.empty-alias-no-step step
  no-path (O.visible-step step rest) = Kernel.empty-alias-no-step step

public-tensor-consumer : TensorVerdict.Test (I ⊗₀ I)
public-tensor-consumer = Example.real-experiment ⊗₁ Example.ideal-experiment

module PublicTensor = Execution public-tensor-consumer

module DisjointExperiments = Disjoint Example.real-experiment Example.ideal-experiment

no-cross-sync : ∀ u v → ¬ (DisjointExperiments.W.Connected
  (DisjointExperiments.T.left u) (DisjointExperiments.T.right v))
no-cross-sync = DisjointExperiments.no-cross-synchronization

no-cross-participants : ∀ {n x q q′ k p j r} (gather : PublicTensor.Gather n x q q′)
  → PublicTensor.Gather.selected gather (inj₁ k) ≡ just p
  → PublicTensor.Gather.selected gather (inj₂ j) ≡ just r → ⊥
no-cross-participants = DisjointExperiments.no-cross-participants

same-traces-different-failures : ∀ xs →
  (KObs.NativeObservation.traces (Evaluation.read UnitVerdict.evaluationᶜˢᵖ Discriminators.ready-network) xs
    → KObs.NativeObservation.traces (Evaluation.read UnitVerdict.evaluationᶜˢᵖ Discriminators.choice-network) xs)
  × (KObs.NativeObservation.traces (Evaluation.read UnitVerdict.evaluationᶜˢᵖ Discriminators.choice-network) xs
    → KObs.NativeObservation.traces (Evaluation.read UnitVerdict.evaluationᶜˢᵖ Discriminators.ready-network) xs)
same-traces-different-failures = Discriminators.identical-traces

failure-separator : ¬ (Evaluation.read UnitVerdict.evaluationᶜˢᵖ Discriminators.ready-network
  KObs.≈ᴼ Evaluation.read UnitVerdict.evaluationᶜˢᵖ Discriminators.choice-network)
failure-separator = Discriminators.evaluation-failure-separator

trace-separator : ¬ (Evaluation.read UnitVerdict.evaluationᶜˢᵖ Discriminators.ready-network
  KObs.≈ᴼ Evaluation.read UnitVerdict.evaluationᶜˢᵖ Discriminators.deadlock-network)
trace-separator = Discriminators.evaluation-trace-separator

divergence-separator : ¬ (Evaluation.read UnitVerdict.evaluationᶜˢᵖ Discriminators.divergence-network
  KObs.≈ᴼ Evaluation.read UnitVerdict.evaluationᶜˢᵖ Discriminators.deadlock-network)
divergence-separator = Discriminators.evaluation-divergence-separator

deadlock-refuses : KObs.NativeObservation.failures
  (Evaluation.read UnitVerdict.evaluationᶜˢᵖ Discriminators.deadlock-network) [] (λ _ → ⊤)
deadlock-refuses = Discriminators.deadlock-refusal

divergence-cannot-refuse : ¬ (KObs.NativeObservation.failures
  (Evaluation.read UnitVerdict.evaluationᶜˢᵖ Discriminators.divergence-network) [] (λ _ → ⊤))
divergence-cannot-refuse = Discriminators.divergence-no-refusal

returned-blocked-no-step : ∀ {l q} →
  ¬ (ReturnedBlocked.K._─[_]→_ ReturnedBlocked.K.initial-configuration l q)
returned-blocked-no-step (ReturnedBlocked.K.internal {k = inj₁ tt} (NL.sSil ()))
returned-blocked-no-step (ReturnedBlocked.K.internal {k = inj₁ tt} (NL.sTau () _))
returned-blocked-no-step (ReturnedBlocked.K.internal {k = inj₂ tt} step) = NL.stop-no-step step
returned-blocked-no-step (ReturnedBlocked.K.exterior {e = inj₁ ()} _ _ _)
returned-blocked-no-step (ReturnedBlocked.K.exterior {e = inj₂ ()} _ _ _)
returned-blocked-no-step (ReturnedBlocked.K.hidden _ gather _ _)
  with ReturnedBlocked.gather-invert gather (inj₁ tt)
... | NL.sVis () _
returned-blocked-no-step (ReturnedBlocked.K.finish _ ready) with ready (inj₂ tt)
... | ()

returned-blocked-no-trace : ¬ (NObs.NativeObservation.traces
  (Evaluation.read NativeClosed.evaluationᶜˢᵖ ReturnedBlocked.network) (ReturnedBlocked.K.√ ∷ []))
returned-blocked-no-trace (q , ReturnedBlockedObs.silent-step step rest) = returned-blocked-no-step step
returned-blocked-no-trace (q , ReturnedBlockedObs.visible-step step rest) = returned-blocked-no-step step

returned-blocked-refuses : NObs.NativeObservation.failures
  (Evaluation.read NativeClosed.evaluationᶜˢᵖ ReturnedBlocked.network) [] (λ _ → ⊤)
returned-blocked-refuses = ReturnedBlocked.K.initial-configuration , ReturnedBlockedObs.done ,
  ((λ _ → returned-blocked-no-step) , (λ _ → returned-blocked-no-step)) ,
  (λ _ _ _ → returned-blocked-no-step)

returned-spinning-diverges : NObs.NativeObservation.divergences
  (Evaluation.read NativeClosed.evaluationᶜˢᵖ ReturnedSpinning.network) []
returned-spinning-diverges = ReturnedSpinning.K.initial-configuration , ReturnedSpinningObs.done ,
  Native.PrivateUnit.returned-spinning-network-divergence

returned-spinning-no-completion : ∀ {q} →
  ¬ (ReturnedSpinning.K._─[_]→_ ReturnedSpinning.K.initial-configuration
    (ReturnedSpinning.K.visible ReturnedSpinning.K.√) q)
returned-spinning-no-completion = Native.PrivateUnit.returned-spinning-no-completion
