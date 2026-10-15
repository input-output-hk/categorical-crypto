{-# OPTIONS --safe --guardedness #-}

-- Native composition hides the binary protocol relay; scheduler commands
-- retain local silent moves, atomic communication and joint termination.
module CategoricalCrypto.CSP.BinaryScheduled (X B : Set) where

open import Data.Empty
open import Data.Maybe.Base
import Data.Maybe.Properties as Maybe
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

import CategoricalCrypto.Channel.Core as C
import CategoricalCrypto.CSP.Process as Process
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Message using (inj₁-inj; inj₂-inj; just-inj; inj₁≢inj₂; just≢nothing; nothing≢just)

module P = Process X B ⊤

data Command : Set where
  leftτ rightτ sync finish : Command

data Label : Set where
  τ √ : Label

data Message : Set where
  offer : X → Message
  rightτ finish : Message

scheduler protocol result : C.Channel
scheduler = Command C.⇿ Label
protocol = Message C.⇿ ⊥
result = Label C.⇿ ⊥

input : ∀ {A B} → C.Channel.inType A ⊎ C.Channel.outType B
  → C.Channel.inType (A M.⊗ᵀ B)
input {A} {B} = C.construct-⊗ {A = A} {B = B C.ᵀ} {m = C.In}

output : ∀ {A B} → Maybe (C.Channel.outType A ⊎ C.Channel.inType B)
  → Maybe (C.Channel.outType (A M.⊗ᵀ B))
output {A} {B} = map (C.construct-⊗ {A = A} {B = B C.ᵀ} {m = C.Out})

data LocalState : Set where
  live : P.Tree → LocalState
  completed : LocalState

data Sender : M.MachineType scheduler protocol LocalState where
  local : ∀ {p p′} → P._─[_]→_ p P.τ p′
    → Sender (live p) (input (inj₁ leftτ)) (output (just (inj₁ τ))) (live p′)
  relay : ∀ {p} → Sender (live p) (input (inj₁ rightτ)) (output (just (inj₂ rightτ))) (live p)
  send : ∀ {p p′ x} → P._─[_]→_ p (P.visible (P.event x)) p′
    → Sender (live p) (input (inj₁ sync)) (output (just (inj₂ (offer x)))) (live p′)
  terminate : ∀ {p} → P.Tree.force p ≡ P.ret tt
    → Sender (live p) (input (inj₁ finish)) (output (just (inj₂ finish))) completed

data Receiver : M.MachineType protocol result LocalState where
  local : ∀ {q q′} → P._─[_]→_ q P.τ q′
    → Receiver (live q) (input (inj₁ rightτ)) (output (just (inj₂ τ))) (live q′)
  receive : ∀ {q q′ x} → P._─[_]→_ q (P.visible (P.event x)) q′
    → Receiver (live q) (input (inj₁ (offer x))) (output (just (inj₂ τ))) (live q′)
  terminate : ∀ {q} → P.Tree.force q ≡ P.ret tt
    → Receiver (live q) (input (inj₁ finish)) (output (just (inj₂ √))) completed

sender : M.Machine scheduler protocol
sender = M.MkMachine Sender

receiver : M.Machine protocol result
receiver = M.MkMachine Receiver

compiled : M.Machine scheduler result
compiled = receiver M.∘ sender

data Joint : M.MachineType scheduler result (LocalState × LocalState) where
  left : ∀ {p p′ q} → P._─[_]→_ p P.τ p′
    → Joint (live p , q) (input (inj₁ leftτ)) (output (just (inj₁ τ))) (live p′ , q)
  right : ∀ {p q q′} → P._─[_]→_ q P.τ q′
    → Joint (live p , live q) (input (inj₁ rightτ)) (output (just (inj₂ τ))) (live p , live q′)
  handshake : ∀ {p p′ q q′ x} → P._─[_]→_ p (P.visible (P.event x)) p′
    → P._─[_]→_ q (P.visible (P.event x)) q′
    → Joint (live p , live q) (input (inj₁ sync)) (output (just (inj₂ τ))) (live p′ , live q′)
  finish : ∀ {p q} → P.Tree.force p ≡ P.ret tt → P.Tree.force q ≡ P.ret tt
    → Joint (live p , live q) (input (inj₁ finish)) (output (just (inj₂ √))) (completed , completed)

specification : M.Machine scheduler result
specification = M.MkMachine Joint


open-machine : M.Machine (scheduler C.⊗₀ protocol) (result C.⊗₀ protocol)
open-machine = M.modifyStepRel M.∘σ (sender M.⊗₁ receiver)

opaque
  unfolding C._⊗₀_ C.destruct-⊗ C.construct-⊗ C.⊗-sym C.⊗-right-intro C.⊗-fusion C.⊗-combine


  joint-to-compiled : ∀ {s i o t} → Joint s i o t → M.Machine.stepRel compiled s i o t
  joint-to-compiled (Joint.left step) = M.Trace[_] (M.Tensor.Step₁ (Sender.local step))
  joint-to-compiled (Joint.right step) = M._Trace∷ᵢ_ (M.Tensor.Step₁ Sender.relay)
    (M.Trace[_] (M.Tensor.Step₂ (Receiver.local step)))
  joint-to-compiled (Joint.handshake sp sq) = M._Trace∷ᵢ_ (M.Tensor.Step₁ (Sender.send sp))
    (M.Trace[_] (M.Tensor.Step₂ (Receiver.receive sq)))
  joint-to-compiled (Joint.finish sp sq) = M._Trace∷ᵢ_ (M.Tensor.Step₁ (Sender.terminate sp))
    (M.Trace[_] (M.Tensor.Step₂ (Receiver.terminate sq)))

  sender-no-refusal : ∀ {p i q} → Sender p i nothing q → ⊥
  sender-no-refusal ()

  receiver-no-refusal : ∀ {p i q} → Receiver p i nothing q → ⊥
  receiver-no-refusal ()

  compiled-to-joint : ∀ {s i o t} → M.Machine.stepRel compiled s i o t → Joint s i o t
  compiled-to-joint {s} {i} {o} {t} path =
    subst (λ w → Joint s i w t) (Maybe.map-id o)
      (start i o (subst (λ w → M.Machine.stepRel compiled s i w t) (sym (Maybe.map-id o)) path))
    where
    extO : Maybe (Label ⊎ Label) → Maybe ((Label ⊎ ⊥) ⊎ (Label ⊎ Message))
    extO nothing = nothing
    extO (just (inj₁ l)) = just (inj₁ (inj₁ l))
    extO (just (inj₂ l)) = just (inj₂ (inj₁ l))

    Response : (s : LocalState × LocalState) → Message → Maybe (Label ⊎ Label)
      → LocalState × LocalState → Set
    Response (p , q) message o t = Σ LocalState (λ q′ → t ≡ (p , q′) ×
      Σ Label (λ l → o ≡ just (inj₂ l) × Receiver q
        (input {protocol} {result} (inj₁ message)) (output {protocol} {result} (just (inj₂ l))) q′))

    reply : ∀ {s t x y} → M.TraceRel open-machine s x y t → (message : Message)
      → (o : Maybe (Label ⊎ Label)) → x ≡ inj₁ (inj₂ message) → y ≡ extO o → Response s message o t
    go : ∀ {s t x y} → M.TraceRel open-machine s x y t → (i : Command ⊎ ⊥)
      → (o : Maybe (Label ⊎ Label)) → x ≡ inj₁ (inj₁ (Data.Sum.Base.[ (λ c → c) , ⊥-elim ] i))
      → y ≡ extO o → Joint s (input {scheduler} {result} i) (output {scheduler} {result} o) t

    start : ∀ {s t} (i : Command ⊎ ⊥) (o : Maybe (Label ⊎ Label))
      → M.Machine.stepRel compiled s (input {scheduler} {result} i) (output {scheduler} {result} o) t
      → Joint s (input {scheduler} {result} i) (output {scheduler} {result} o) t
    start (inj₂ ()) o path
    start (inj₁ command) nothing path = go path (inj₁ command) nothing refl refl
    start (inj₁ command) (just (inj₁ l)) path = go path (inj₁ command) (just (inj₁ l)) refl refl
    start (inj₁ command) (just (inj₂ l)) path = go path (inj₁ command) (just (inj₂ l)) refl refl

    reply (M.Trace[_] step) message (just (inj₁ l)) refl refl with M.comp-view step
    ... | inj₁ (_ , _ , eq , _) = inj₁≢inj₂ (sym eq)
    ... | inj₂ (_ , nothing , _ , eq , _) = just≢nothing eq
    ... | inj₂ (_ , just _ , _ , eq , _) = inj₁≢inj₂ (just-inj eq)
    reply {s = p , q} {t = p′ , q′} (M.Trace[_] step) message (just (inj₂ l)) refl refl
      with M.comp-view step
    ... | inj₁ (_ , _ , eq , _) = inj₁≢inj₂ (sym eq)
    ... | inj₂ (_ , nothing , _ , eq , _) = just≢nothing eq
    ... | inj₂ (i , just o , ieq , oeq , seq , r) with inj₂-inj ieq | inj₂-inj (just-inj oeq) | seq
    ... | refl | refl | refl = q′ , refl , l , refl , r
    reply (M.Trace[_] step) message nothing refl refl with M.comp-view step
    ... | inj₁ (_ , _ , eq , _) = inj₁≢inj₂ (sym eq)
    ... | inj₂ (_ , just _ , _ , eq , _) = nothing≢just eq
    ... | inj₂ (_ , nothing , _ , _ , _ , r) = ⊥-elim (receiver-no-refusal r)
    reply (M._Trace∷ₒ_ {outC = ()} step rest) message o eq eq′
    reply (M._Trace∷ᵢ_ step rest) message o refl refl with M.comp-view step
    ... | inj₁ (_ , _ , eq , _) = inj₁≢inj₂ (sym eq)
    ... | inj₂ (_ , nothing , _ , eq , _) = just≢nothing eq
    ... | inj₂ (_ , just _ , _ , eq , _) = inj₁≢inj₂ (just-inj eq)

    go path (inj₂ ()) o eq eq′
    go {s = p , q} {t = p′ , q′} (M.Trace[_] step) (inj₁ command) (just (inj₁ l)) refl refl
      with M.comp-view step
    ... | inj₂ (_ , _ , eq , _) = inj₁≢inj₂ eq
    ... | inj₁ (_ , nothing , _ , eq , _) = just≢nothing eq
    ... | inj₁ (i , just o , ieq , oeq , seq , r) with inj₁-inj ieq | inj₁-inj (just-inj oeq) | seq
    ... | refl | refl | refl with r
    ... | Sender.local move = Joint.left move
    go (M.Trace[_] step) (inj₁ command) (just (inj₂ l)) refl refl with M.comp-view step
    ... | inj₂ (_ , _ , eq , _) = inj₁≢inj₂ eq
    ... | inj₁ (_ , nothing , _ , eq , _) = just≢nothing eq
    ... | inj₁ (_ , just _ , _ , eq , _) = inj₁≢inj₂ (sym (just-inj eq))
    go (M.Trace[_] step) (inj₁ command) nothing refl refl with M.comp-view step
    ... | inj₂ (_ , _ , eq , _) = inj₁≢inj₂ eq
    ... | inj₁ (_ , just _ , _ , eq , _) = nothing≢just eq
    ... | inj₁ (_ , nothing , _ , _ , _ , r) = ⊥-elim (sender-no-refusal r)
    go (M._Trace∷ₒ_ {outC = ()} step rest) i o eq eq′
    go {s = p , q} (M._Trace∷ᵢ_ {s' = p′ , q′} {inC = message} step rest)
      (inj₁ command) o refl refl with M.comp-view step
    ... | inj₂ (_ , _ , eq , _) = inj₁≢inj₂ eq
    ... | inj₁ (_ , nothing , _ , eq , _) = just≢nothing eq
    ... | inj₁ (i , just out , ieq , oeq , seq , r) with inj₁-inj ieq | inj₁-inj (just-inj oeq) | seq
    ... | refl | refl | refl with reply rest message o refl refl
    ... | q″ , refl , l , refl , received with r | received
    ... | Sender.relay | Receiver.local move = Joint.right move
    ... | Sender.send sp | Receiver.receive sq = Joint.handshake sp sq
    ... | Sender.terminate sp | Receiver.terminate sq = Joint.finish sp sq

  completed-no-step : ∀ {i o t} → M.Machine.stepRel compiled (completed , completed) i o t → ⊥
  completed-no-step {i} {o} path with compiled-to-joint {i = i} {o = o} path
  ... | ()

  sync-disabled : ∀ {p q o t}
    → (∀ {x p′} → P._─[_]→_ p (P.visible (P.event x)) p′ → ⊥)
    → M.Machine.stepRel compiled (live p , live q) (input {scheduler} {result} (inj₁ sync)) o t → ⊥
  sync-disabled {o = o} disabled path with compiled-to-joint
    {i = input {scheduler} {result} (inj₁ sync)} {o = o} path
  ... | Joint.handshake sp sq = disabled sp

  sync-disabled-right : ∀ {p q o t}
    → (∀ {x q′} → P._─[_]→_ q (P.visible (P.event x)) q′ → ⊥)
    → M.Machine.stepRel compiled (live p , live q) (input {scheduler} {result} (inj₁ sync)) o t → ⊥
  sync-disabled-right {o = o} disabled path with compiled-to-joint
    {i = input {scheduler} {result} (inj₁ sync)} {o = o} path
  ... | Joint.handshake sp sq = disabled sq

  finish-disabled-right : ∀ {p q o t} → (P.Tree.force q ≡ P.ret tt → ⊥)
    → M.Machine.stepRel compiled (live p , live q) (input {scheduler} {result} (inj₁ Command.finish)) o t → ⊥
  finish-disabled-right {o = o} disabled path with compiled-to-joint
    {i = input {scheduler} {result} (inj₁ Command.finish)} {o = o} path
  ... | Joint.finish sp sq = disabled sq

  left-disabled : ∀ {p q o t} → (∀ {p′} → P._─[_]→_ p P.τ p′ → ⊥)
    → M.Machine.stepRel compiled (live p , live q) (input {scheduler} {result} (inj₁ leftτ)) o t → ⊥
  left-disabled {o = o} disabled path with compiled-to-joint
    {i = input {scheduler} {result} (inj₁ leftτ)} {o = o} path
  ... | Joint.left move = disabled move
