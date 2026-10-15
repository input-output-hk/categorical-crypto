{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.CSP.BinaryScheduledTests where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

import CategoricalCrypto.Channel.Core as C
open import CategoricalCrypto.CSP.BinaryPresented
open import CategoricalCrypto.CSP.BinaryPresentedSource
import CategoricalCrypto.CSP.BinaryOperational as Operational
import CategoricalCrypto.CSP.BinaryDivergence as Divergence
import CategoricalCrypto.Machine.Core as M
import CategoricalCrypto.Machine.Initialized as I
import CategoricalCrypto.Machine.Relational as R
import CategoricalCrypto.Machine.Relational.Wiring as W
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive
open import CategoricalCrypto.Machine.Relational.Presentation

module Native = Operational Bool ⊤
module Source = Native.Connection sender-tree receiver-tree
module D = Divergence Bool ⊤
module Silent = D.Divergence sender-tree receiver-tree

finite : R.Initialized S.scheduler S.result
finite = receiver W.∘ sender

presented : R.Initialized S.scheduler S.result
presented = shadow receiver-presentation W.∘ shadow sender-presentation

presented-wiring-correct : presented R.≈ᴿ finite
presented-wiring-correct = W.∘-cong (presentation-correct receiver-presentation) (presentation-correct sender-presentation)

source-and-presented-wiring : Source.scheduled R.≈ᴿ presented
source-and-presented-wiring = R.≈ᴿ-trans Source.native-components-correct
  (R.≈ᴿ-trans (R.≈ᴿ-sym independent-component-compilation) (R.≈ᴿ-sym presented-wiring-correct))

data Acknowledgement : Set where
  exchange-ack finished : Acknowledgement

context-channel : C.Channel
context-channel = Acknowledgement C.⇿ ⊥

context-output : Acknowledgement → C.Channel.outType (S.result M.⊗ᵀ context-channel)
context-output ack = C.construct-⊗ {A = S.result} {B = context-channel C.ᵀ} {m = C.Out} (inj₂ ack)

data ContextStep : M.MachineType S.result context-channel Bool where
  exchange : ∀ {seen} → ContextStep seen (S.input (inj₁ S.τ)) (just (context-output exchange-ack)) true
  finish : ContextStep true (S.input (inj₁ S.√)) (just (context-output finished)) false

context : R.Initialized S.result context-channel
context = R.singleton (M.MkMachine ContextStep) false

context-respects-presented-wiring : (context W.∘ presented) R.≈ᴿ (context W.∘ finite)
context-respects-presented-wiring = W.∘-cong R.≈ᴿ-refl presented-wiring-correct

opaque
  unfolding C._⊗₀_ C.destruct-⊗ C.construct-⊗ C.⊗-sym C.⊗-right-intro C.⊗-fusion C.⊗-combine

  false-exchange : M.Machine.stepRel (R.machine finite) (SendState.ready , ReceiveState.ready)
    (S.input {S.scheduler} {S.result} (inj₁ S.sync)) (S.output {S.scheduler} {S.result} (just (inj₂ S.τ)))
    (SendState.returned , ReceiveState.returned)
  false-exchange = M._Trace∷ᵢ_ (M.Tensor.Step₁ choose-false) (M.Trace[_] (M.Tensor.Step₂ false-branch))

  true-exchange : M.Machine.stepRel (R.machine finite) (SendState.ready , ReceiveState.ready)
    (S.input {S.scheduler} {S.result} (inj₁ S.sync)) (S.output {S.scheduler} {S.result} (just (inj₂ S.τ)))
    (SendState.returned , ReceiveState.looping)
  true-exchange = M._Trace∷ᵢ_ (M.Tensor.Step₁ choose-true) (M.Trace[_] (M.Tensor.Step₂ true-branch))

  joint-termination : M.Machine.stepRel (R.machine finite) (SendState.returned , ReceiveState.returned)
    (S.input {S.scheduler} {S.result} (inj₁ S.finish)) (S.output {S.scheduler} {S.result} (just (inj₂ S.√)))
    (SendState.done , ReceiveState.done)
  joint-termination = M._Trace∷ᵢ_ (M.Tensor.Step₁ SendStep.terminate) (M.Trace[_] (M.Tensor.Step₂ ReceiveStep.terminate))

  communication-controlled-loop : M.Machine.stepRel (R.machine finite) (SendState.returned , ReceiveState.looping)
    (S.input {S.scheduler} {S.result} (inj₁ S.rightτ)) (S.output {S.scheduler} {S.result} (just (inj₂ S.τ)))
    (SendState.returned , ReceiveState.looping)
  communication-controlled-loop = M._Trace∷ᵢ_ (M.Tensor.Step₁ relay-returned) (M.Trace[_] (M.Tensor.Step₂ loop))

  false-finite-execution : R.Executes finite
    ((S.input {S.scheduler} {S.result} (inj₁ S.sync) , S.output {S.scheduler} {S.result} (just (inj₂ S.τ))) ∷
     (S.input {S.scheduler} {S.result} (inj₁ S.finish) , S.output {S.scheduler} {S.result} (just (inj₂ S.√))) ∷ [])
  false-finite-execution = _ , (refl , refl) , _ , I.next false-exchange (I.next joint-termination I.done)

  presented-finite-execution : R.Executes presented
    ((S.input {S.scheduler} {S.result} (inj₁ S.sync) , S.output {S.scheduler} {S.result} (just (inj₂ S.τ))) ∷
     (S.input {S.scheduler} {S.result} (inj₁ S.finish) , S.output {S.scheduler} {S.result} (just (inj₂ S.√))) ∷ [])
  presented-finite-execution = R.executes-from presented-wiring-correct false-finite-execution

  context-exchange : M.Machine.stepRel (R.machine (context W.∘ finite))
    ((SendState.ready , ReceiveState.ready) , false)
    (S.input {S.scheduler} {context-channel} (inj₁ S.sync))
    (S.output {S.scheduler} {context-channel} (just (inj₂ exchange-ack)))
    ((SendState.returned , ReceiveState.returned) , true)
  context-exchange = M._Trace∷ᵢ_ (M.Tensor.Step₁ false-exchange) (M.Trace[_] (M.Tensor.Step₂ ContextStep.exchange))

  context-termination : M.Machine.stepRel (R.machine (context W.∘ finite))
    ((SendState.returned , ReceiveState.returned) , true)
    (S.input {S.scheduler} {context-channel} (inj₁ S.finish))
    (S.output {S.scheduler} {context-channel} (just (inj₂ finished)))
    ((SendState.done , ReceiveState.done) , false)
  context-termination = M._Trace∷ᵢ_ (M.Tensor.Step₁ joint-termination) (M.Trace[_] (M.Tensor.Step₂ ContextStep.finish))

  context-finite-execution : R.Executes (context W.∘ finite)
    ((S.input {S.scheduler} {context-channel} (inj₁ S.sync) , S.output {S.scheduler} {context-channel} (just (inj₂ exchange-ack))) ∷
     (S.input {S.scheduler} {context-channel} (inj₁ S.finish) , S.output {S.scheduler} {context-channel} (just (inj₂ finished))) ∷ [])
  context-finite-execution = _ , ((refl , refl) , refl) , _ , I.next context-exchange (I.next context-termination I.done)

  presented-context-finite-execution : R.Executes (context W.∘ presented)
    ((S.input {S.scheduler} {context-channel} (inj₁ S.sync) , S.output {S.scheduler} {context-channel} (just (inj₂ exchange-ack))) ∷
     (S.input {S.scheduler} {context-channel} (inj₁ S.finish) , S.output {S.scheduler} {context-channel} (just (inj₂ finished))) ∷ [])
  presented-context-finite-execution = R.executes-from context-respects-presented-wiring context-finite-execution

  no-unsolicited-completion : ∀ {o q} → ¬ (ContextStep false (S.input {S.result} {context-channel} (inj₁ S.√)) o q)
  no-unsolicited-completion ()

  no-finish-after-true : ∀ {o t} → ¬ (M.Machine.stepRel S.compiled
    (S.live (P.return tt) , S.live P.div) (S.input {S.scheduler} {S.result} (inj₁ S.finish)) o t)
  no-finish-after-true {o} = S.finish-disabled-right {o = o} (λ ())

  no-resynchronization : ∀ {o t} → ¬ (M.Machine.stepRel S.compiled
    (S.live (P.return tt) , S.live (P.return tt)) (S.input {S.scheduler} {S.result} (inj₁ S.sync)) o t)
  no-resynchronization {o} = S.sync-disabled {o = o} (λ { (P.sVis () offered) })

  sender-no-silent : ∀ {p′} → P._─[_]→_ sender-tree P.τ p′ → ⊥
  sender-no-silent (P.sSil ())
  sender-no-silent (P.sTau refl ())

  no-initial-left-command : ∀ {o t} → ¬ (M.Machine.stepRel S.compiled
    (S.live sender-tree , S.live receiver-tree) (S.input {S.scheduler} {S.result} (inj₁ S.leftτ)) o t)
  no-initial-left-command {o} = S.left-disabled {o = o} sender-no-silent

  true-branch-diverges : Silent.CompiledDiverges (S.live (P.return tt) , S.live P.div)
  Silent.CompiledDiverges.next true-branch-diverges = S.live (P.return tt) , S.live P.div
  Silent.CompiledDiverges.command true-branch-diverges = S.input {S.scheduler} {S.result} (inj₁ S.rightτ)
  Silent.CompiledDiverges.side true-branch-diverges = false
  Silent.CompiledDiverges.step true-branch-diverges = S.joint-to-compiled (S.Joint.right (P.sSil refl))
  Silent.CompiledDiverges.rest true-branch-diverges = true-branch-diverges

  native-communication-controlled-divergence : Source.E.Diverges
    (Source.E.running (Source.pair (P.return tt) P.div))
  native-communication-controlled-divergence = Silent.unschedule-divergence
    (Silent.uncompile-divergence (_ , Source.running refl refl , refl) true-branch-diverges)

  native-true-exchange : Source.E._─[_]→_ Source.E.initial-configuration Source.E.τ
    (Source.E.running (Source.pair (P.return tt) P.div))
  native-true-exchange = Source.E.hidden true g (λ { (inj₁ ()) ; (inj₂ ()) }) (Source.handshake g)
    where
    g : Source.E.Gather (inj₁ tt) true Source.W.initial-state (Source.pair (P.return tt) P.div)
    g = Source.gather-state (P.sVis refl refl) (P.sVis refl refl)

  source-finite-execution : R.Executes Source.scheduled
    ((S.input {S.scheduler} {S.result} (inj₁ S.sync) , S.output {S.scheduler} {S.result} (just (inj₂ S.τ))) ∷
     (S.input {S.scheduler} {S.result} (inj₁ S.finish) , S.output {S.scheduler} {S.result} (just (inj₂ S.√))) ∷ [])
  source-finite-execution = R.executes-from source-and-presented-wiring presented-finite-execution

  context-distribution : Bool → S.Label ⊎ ⊥
    → Dₚ (Bool × C.Channel.outType (S.result M.⊗ᵀ context-channel))
  context-distribution seen (inj₁ S.τ) = returnₚ (true , context-output exchange-ack)
  context-distribution true (inj₁ S.√) = returnₚ (false , context-output finished)
  context-distribution false (inj₁ S.√) = botₚ
  context-distribution _ (inj₂ ())

  context-sound : ∀ {s′ o} (s : Bool) (i : S.Label ⊎ ⊥)
    → Positive (context-distribution s i) (s′ , o)
    → ContextStep s (S.input {S.result} {context-channel} i) (just o) s′
  context-sound s (inj₁ S.τ) path with positive-return-reflect path
  ... | refl = ContextStep.exchange
  context-sound true (inj₁ S.√) path with positive-return-reflect path
  ... | refl = ContextStep.finish
  context-sound false (inj₁ S.√) path = ⊥-elim (positive-bot path)
  context-sound _ (inj₂ ()) path

  context-complete : ∀ {s i o s′} → ContextStep s i (just o) s′
    → Positive (context-distribution s (C.destruct-⊗ {A = S.result} {B = context-channel C.ᵀ} {m = C.In} i)) (s′ , o)
  context-complete ContextStep.exchange = positive-return _
  context-complete ContextStep.finish = positive-return _

  context-presentation : Presentation context
  context-presentation = record
    { initialₚ = returnₚ false
    ; stepₚ = λ s i → context-distribution s (C.destruct-⊗ {A = S.result} {B = context-channel C.ᵀ} {m = C.In} i)
    ; initial-sound = positive-return-reflect
    ; initial-complete = λ { refl → positive-return _ }
    ; step-sound = λ { {s} {i} → context-sound s i }
    ; step-complete = context-complete
    ; no-refusal = λ () }

  blocked-listener-cannot-leak : ∀ {o t} → ¬ (M.Machine.stepRel S.compiled
    (S.live sender-tree , S.live P.stop) (S.input {S.scheduler} {S.result} (inj₁ S.sync)) o t)
  blocked-listener-cannot-leak {o} = S.sync-disabled-right {o = o} P.stop-no-step

  local-left-silent-move : M.Machine.stepRel S.compiled
    (S.live (P.silent (P.return tt)) , S.live (P.return tt))
    (S.input {S.scheduler} {S.result} (inj₁ S.leftτ)) (S.output {S.scheduler} {S.result} (just (inj₁ S.τ)))
    (S.live (P.return tt) , S.live (P.return tt))
  local-left-silent-move = S.joint-to-compiled (S.Joint.left (P.sSil refl))
