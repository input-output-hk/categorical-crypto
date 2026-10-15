{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.CSP.BinaryPresentedSource where

open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.BinaryPresented
import CategoricalCrypto.Machine.Relational as R
import CategoricalCrypto.Machine.Relational.Wiring as W

module P = S.P

sender-tree receiver-tree : P.Tree
sender-tree = P.menu (λ _ → just (P.return tt)) (λ _ → nothing)
receiver-tree = P.menu (λ { (_ , false) → just (P.return tt) ; (_ , true) → just P.div }) (λ _ → nothing)

decode-send : SendState → S.LocalState
decode-send SendState.ready = S.live sender-tree
decode-send SendState.returned = S.live (P.return tt)
decode-send SendState.done = S.completed

decode-receive : ReceiveState → S.LocalState
decode-receive ReceiveState.ready = S.live receiver-tree
decode-receive ReceiveState.returned = S.live (P.return tt)
decode-receive ReceiveState.looping = S.live P.div
decode-receive ReceiveState.done = S.completed

send-to : ∀ {s i o s′} → SendStep s i o s′ → S.Sender (decode-send s) i o (decode-send s′)
send-to choose-false = S.send (P.sVis refl refl)
send-to choose-true = S.send (P.sVis refl refl)
send-to relay-ready = S.relay
send-to relay-returned = S.relay
send-to SendStep.terminate = S.Sender.terminate refl

send-from : ∀ {s i o t} → S.Sender (decode-send s) i o t
  → ∃ λ s′ → SendStep s i o s′ × decode-send s′ ≡ t
send-from {SendState.ready} (S.Sender.local (P.sSil ()))
send-from {SendState.ready} (S.Sender.local (P.sTau refl ()))
send-from {SendState.ready} S.relay = _ , relay-ready , refl
send-from {SendState.ready} (S.send {x = tt , false} (P.sVis refl refl)) = _ , choose-false , refl
send-from {SendState.ready} (S.send {x = tt , true} (P.sVis refl refl)) = _ , choose-true , refl
send-from {SendState.ready} (S.Sender.terminate ())
send-from {SendState.returned} (S.Sender.local (P.sSil ()))
send-from {SendState.returned} (S.Sender.local (P.sTau () offered))
send-from {SendState.returned} S.relay = _ , relay-returned , refl
send-from {SendState.returned} (S.send (P.sVis () offered))
send-from {SendState.returned} (S.Sender.terminate refl) = _ , SendStep.terminate , refl
send-from {SendState.done} ()

receive-to : ∀ {s i o s′} → ReceiveStep s i o s′ → S.Receiver (decode-receive s) i o (decode-receive s′)
receive-to false-branch = S.receive (P.sVis refl refl)
receive-to true-branch = S.receive (P.sVis refl refl)
receive-to loop = S.Receiver.local (P.sSil refl)
receive-to ReceiveStep.terminate = S.Receiver.terminate refl

receive-from : ∀ {s i o t} → S.Receiver (decode-receive s) i o t
  → ∃ λ s′ → ReceiveStep s i o s′ × decode-receive s′ ≡ t
receive-from {ReceiveState.ready} (S.Receiver.local (P.sSil ()))
receive-from {ReceiveState.ready} (S.Receiver.local (P.sTau refl ()))
receive-from {ReceiveState.ready} (S.receive {x = tt , false} (P.sVis refl refl)) = _ , false-branch , refl
receive-from {ReceiveState.ready} (S.receive {x = tt , true} (P.sVis refl refl)) = _ , true-branch , refl
receive-from {ReceiveState.ready} (S.Receiver.terminate ())
receive-from {ReceiveState.returned} (S.Receiver.local (P.sSil ()))
receive-from {ReceiveState.returned} (S.Receiver.local (P.sTau () offered))
receive-from {ReceiveState.returned} (S.receive (P.sVis () offered))
receive-from {ReceiveState.returned} (S.Receiver.terminate refl) = _ , ReceiveStep.terminate , refl
receive-from {ReceiveState.looping} (S.Receiver.local (P.sSil refl)) = _ , loop , refl
receive-from {ReceiveState.looping} (S.Receiver.local (P.sTau () offered))
receive-from {ReceiveState.looping} (S.receive (P.sVis () offered))
receive-from {ReceiveState.looping} (S.Receiver.terminate ())
receive-from {ReceiveState.done} ()

sender-correct : sender R.≈ᴿ R.singleton S.sender (S.live sender-tree)
sender-correct = record
  { Related = λ s t → decode-send s ≡ t
  ; initial-to = λ { refl → _ , refl , refl }
  ; initial-from = λ { refl → _ , refl , refl }
  ; step-to = λ { refl step → _ , send-to step , refl }
  ; step-from = λ { refl step → send-from step } }

receiver-correct : receiver R.≈ᴿ R.singleton S.receiver (S.live receiver-tree)
receiver-correct = record
  { Related = λ s t → decode-receive s ≡ t
  ; initial-to = λ { refl → _ , refl , refl }
  ; initial-from = λ { refl → _ , refl , refl }
  ; step-to = λ { refl step → _ , receive-to step , refl }
  ; step-from = λ { refl step → receive-from step } }

independent-component-compilation : (receiver W.∘ sender) R.≈ᴿ
  ((R.singleton S.receiver (S.live receiver-tree)) W.∘ (R.singleton S.sender (S.live sender-tree)))
independent-component-compilation = W.∘-cong receiver-correct sender-correct
