{-# OPTIONS --safe --guardedness #-}

-- Both payloads have positive weight. The true branch enables silent looping;
-- the false branch permits joint termination. Disabled commands have no path.
module CategoricalCrypto.CSP.BinaryPresented where

open import Data.Bool.Base
open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base hiding (map)
open import Data.Rational as ℚ using (0ℚ; ½)
open import Data.Rational.Properties
open import Data.Sum.Base hiding (map)
open import Data.Sum.Properties using (inj₁-injective)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (toWitness)

import CategoricalCrypto.Channel.Core as C
import CategoricalCrypto.CSP.BinaryScheduled as Binary
import CategoricalCrypto.Machine.Core as M
import CategoricalCrypto.Machine.Relational as R
open import CategoricalCrypto.Machine.Relational.Presentation
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive

module S = Binary (⊤ × Bool) ⊤

private
  half-positive : 0ℚ ℚ.< ½
  half-positive = toWitness {a? = 0ℚ ℚ.<? ½} tt

  half-nonnegative : 0ℚ ℚ.≤ ½
  half-nonnegative = <⇒≤ half-positive

two : ∀ {A : Set} → A → A → Dₚ A
two x y = record
  { wt = λ _ → ½ ; wt-nn = λ _ → half-nonnegative ; wt-1 = refl
  ; br = λ { true → inj₁ x ; false → inj₁ y } }

two-sound : ∀ {A : Set} {x y z : A} → Positive (two x y) z → x ≡ z ⊎ y ≡ z
two-sound (hit true pos eq) = inj₁ (inj₁-injective eq)
two-sound (hit false pos eq) = inj₂ (inj₁-injective eq)
two-sound (delay true e pos () rest)
two-sound (delay false e pos () rest)


data SendState : Set where
  ready returned done : SendState

data ReceiveState : Set where
  ready returned looping done : ReceiveState

send-output : S.Message → C.Channel.outType (S.scheduler M.⊗ᵀ S.protocol)
send-output message = C.construct-⊗ {A = S.scheduler} {B = S.protocol C.ᵀ} {m = C.Out} (inj₂ message)

receive-output : S.Label → C.Channel.outType (S.protocol M.⊗ᵀ S.result)
receive-output label = C.construct-⊗ {A = S.protocol} {B = S.result C.ᵀ} {m = C.Out} (inj₂ label)

data SendStep : M.MachineType S.scheduler S.protocol SendState where
  choose-false : SendStep ready (S.input (inj₁ S.sync)) (just (send-output (S.offer (tt , false)))) returned
  choose-true : SendStep ready (S.input (inj₁ S.sync)) (just (send-output (S.offer (tt , true)))) returned
  relay-ready : SendStep ready (S.input (inj₁ S.rightτ)) (just (send-output S.rightτ)) ready
  relay-returned : SendStep returned (S.input (inj₁ S.rightτ)) (just (send-output S.rightτ)) returned
  terminate : SendStep returned (S.input (inj₁ S.finish)) (just (send-output S.finish)) done

data ReceiveStep : M.MachineType S.protocol S.result ReceiveState where
  false-branch : ReceiveStep ready (S.input (inj₁ (S.offer (tt , false)))) (just (receive-output S.τ)) returned
  true-branch : ReceiveStep ready (S.input (inj₁ (S.offer (tt , true)))) (just (receive-output S.τ)) looping
  loop : ReceiveStep looping (S.input (inj₁ S.rightτ)) (just (receive-output S.τ)) looping
  terminate : ReceiveStep returned (S.input (inj₁ S.finish)) (just (receive-output S.√)) done

sender : R.Initialized S.scheduler S.protocol
sender = R.singleton (M.MkMachine SendStep) SendState.ready

receiver : R.Initialized S.protocol S.result
receiver = R.singleton (M.MkMachine ReceiveStep) ReceiveState.ready

send-distribution : SendState → S.Command ⊎ ⊥
  → Dₚ (SendState × C.Channel.outType (S.scheduler M.⊗ᵀ S.protocol))
send-distribution SendState.ready (inj₁ S.sync) = two
  (SendState.returned , send-output (S.offer (tt , false))) (SendState.returned , send-output (S.offer (tt , true)))
send-distribution SendState.ready (inj₁ S.rightτ) = returnₚ (SendState.ready , send-output S.rightτ)
send-distribution SendState.returned (inj₁ S.rightτ) = returnₚ (SendState.returned , send-output S.rightτ)
send-distribution SendState.returned (inj₁ S.finish) = returnₚ (SendState.done , send-output S.finish)
send-distribution _ _ = botₚ

receive-distribution : ReceiveState → S.Message ⊎ ⊥
  → Dₚ (ReceiveState × C.Channel.outType (S.protocol M.⊗ᵀ S.result))
receive-distribution ReceiveState.ready (inj₁ (S.offer (tt , false))) = returnₚ (ReceiveState.returned , receive-output S.τ)
receive-distribution ReceiveState.ready (inj₁ (S.offer (tt , true))) = returnₚ (ReceiveState.looping , receive-output S.τ)
receive-distribution ReceiveState.looping (inj₁ S.rightτ) = returnₚ (ReceiveState.looping , receive-output S.τ)
receive-distribution ReceiveState.returned (inj₁ S.finish) = returnₚ (ReceiveState.done , receive-output S.√)
receive-distribution _ _ = botₚ

opaque
  unfolding C._⊗₀_ C.construct-⊗ C.destruct-⊗

  send-sound : ∀ {s′ o} (s : SendState) (i : S.Command ⊎ ⊥)
    → Positive (send-distribution s i) (s′ , o)
    → SendStep s (S.input {S.scheduler} {S.protocol} i) (just o) s′
  send-sound _ (inj₂ ()) path
  send-sound SendState.ready (inj₁ S.sync) path with two-sound path
  ... | inj₁ refl = choose-false
  ... | inj₂ refl = choose-true
  send-sound SendState.ready (inj₁ S.rightτ) path with positive-return-reflect path
  ... | refl = relay-ready
  send-sound SendState.returned (inj₁ S.rightτ) path with positive-return-reflect path
  ... | refl = relay-returned
  send-sound SendState.returned (inj₁ S.finish) path with positive-return-reflect path
  ... | refl = SendStep.terminate
  send-sound SendState.ready (inj₁ S.leftτ) path = ⊥-elim (positive-bot path)
  send-sound SendState.ready (inj₁ S.finish) path = ⊥-elim (positive-bot path)
  send-sound SendState.returned (inj₁ S.leftτ) path = ⊥-elim (positive-bot path)
  send-sound SendState.returned (inj₁ S.sync) path = ⊥-elim (positive-bot path)
  send-sound SendState.done i path = ⊥-elim (positive-bot path)

  send-complete : ∀ {s i o s′} → SendStep s i (just o) s′
    → Positive (send-distribution s (C.destruct-⊗ {m = C.In} i)) (s′ , o)
  send-complete choose-false = hit true half-positive refl
  send-complete choose-true = hit false half-positive refl
  send-complete relay-ready = positive-return _
  send-complete relay-returned = positive-return _
  send-complete SendStep.terminate = positive-return _

  sender-presentation : Presentation sender
  sender-presentation = record
    { initialₚ = returnₚ SendState.ready
    ; stepₚ = λ s i → send-distribution s (C.destruct-⊗ {A = S.scheduler} {B = S.protocol C.ᵀ} {m = C.In} i)
    ; initial-sound = positive-return-reflect
    ; initial-complete = λ { refl → positive-return _ }
    ; step-sound = λ { {s} {i} → send-sound s i }
    ; step-complete = send-complete
    ; no-refusal = λ () }

  receive-sound : ∀ {s′ o} (s : ReceiveState) (i : S.Message ⊎ ⊥)
    → Positive (receive-distribution s i) (s′ , o)
    → ReceiveStep s (S.input {S.protocol} {S.result} i) (just o) s′
  receive-sound _ (inj₂ ()) path
  receive-sound ReceiveState.ready (inj₁ (S.offer (tt , false))) path with positive-return-reflect path
  ... | refl = false-branch
  receive-sound ReceiveState.ready (inj₁ (S.offer (tt , true))) path with positive-return-reflect path
  ... | refl = true-branch
  receive-sound ReceiveState.looping (inj₁ S.rightτ) path with positive-return-reflect path
  ... | refl = loop
  receive-sound ReceiveState.returned (inj₁ S.finish) path with positive-return-reflect path
  ... | refl = ReceiveStep.terminate
  receive-sound ReceiveState.ready (inj₁ S.rightτ) path = ⊥-elim (positive-bot path)
  receive-sound ReceiveState.ready (inj₁ S.finish) path = ⊥-elim (positive-bot path)
  receive-sound ReceiveState.returned (inj₁ (S.offer x)) path = ⊥-elim (positive-bot path)
  receive-sound ReceiveState.returned (inj₁ S.rightτ) path = ⊥-elim (positive-bot path)
  receive-sound ReceiveState.looping (inj₁ (S.offer x)) path = ⊥-elim (positive-bot path)
  receive-sound ReceiveState.looping (inj₁ S.finish) path = ⊥-elim (positive-bot path)
  receive-sound ReceiveState.done i path = ⊥-elim (positive-bot path)

  receive-complete : ∀ {s i o s′} → ReceiveStep s i (just o) s′
    → Positive (receive-distribution s (C.destruct-⊗ {m = C.In} i)) (s′ , o)
  receive-complete false-branch = positive-return _
  receive-complete true-branch = positive-return _
  receive-complete loop = positive-return _
  receive-complete ReceiveStep.terminate = positive-return _

  receiver-presentation : Presentation receiver
  receiver-presentation = record
    { initialₚ = returnₚ ReceiveState.ready
    ; stepₚ = λ s i → receive-distribution s (C.destruct-⊗ {A = S.protocol} {B = S.result C.ᵀ} {m = C.In} i)
    ; initial-sound = positive-return-reflect
    ; initial-complete = λ { refl → positive-return _ }
    ; step-sound = λ { {s} {i} → receive-sound s i }
    ; step-complete = receive-complete
    ; no-refusal = λ () }
