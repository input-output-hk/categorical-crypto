{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.TaskPIOA.MarkerTests where

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.SSP.Dist.Kernel using (none)
import CategoricalCrypto.SSP.Dist.SchedulerInformation as Information
open import CategoricalCrypto.SSP.Iface using (Ωᴵ)
open import CategoricalCrypto.SSP.Observation using (runᵖ)
import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.TaskPIOA.Adaptive
open import CategoricalCrypto.TaskPIOA.AdaptiveFinite
import CategoricalCrypto.TaskPIOA.AdaptiveTests
open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.Marker
open import CategoricalCrypto.TaskPIOA.Product
open import CategoricalCrypto.TaskPIOA.SSPAdapter using (Tick; resource)
import CategoricalCrypto.TaskPIOA.Setup as Source
open import CategoricalCrypto.TaskPIOA.Simulation
import CategoricalCrypto.TaskPIOA.Tests as Native
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E; maybeℚ)
open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool)

four : Schedule pulseSignature
four = tt ∷ tt ∷ tt ∷ tt ∷ []

correlated : List (Maybe ⊤) → ℚ
correlated (nothing ∷ nothing ∷ just _ ∷ nothing ∷ []) = 1ℚ
correlated (nothing ∷ just _ ∷ nothing ∷ just _ ∷ []) = 1ℚ
correlated _ = 0ℚ

generic-marker-alternating : Source.evaluate (markerTest four correlated) alternating ≡ 1ℚ
generic-marker-alternating = refl

generic-marker-grouped : Source.evaluate (markerTest four correlated) grouped ≡ 0ℚ
generic-marker-grouped = refl

generic-source-agreement : Source.evaluate (markerTest four correlated) alternating
  ≡ lookupᴰℚ (entries (paddedReplyRun alternating four (initial alternating))) correlated
generic-source-agreement = marker-test-agreement alternating four correlated

openSignature : Signature
openSignature = record
  { inputs = bit ; outputs = one ; hidden = empty ; tasks = one
  ; taskOf = λ _ → tt ; task-inhabited = λ _ → inj₁ tt , refl }

openMachine : Automaton openSignature
openMachine = record
  { states = one ; initial = tt ; input = λ _ _ → return-ℚ tt
  ; choose = λ _ _ → just (inj₁ tt) ; owns = λ _ _ _ _ → refl
  ; kernel = λ _ _ → return-ℚ tt }

oneOutput : List (Maybe ⊤) → ℚ
oneOutput (just tt ∷ []) = 1ℚ
oneOutput _ = 0ℚ

open-input-marker-test : Source.evaluate (markerTest (tt ∷ []) oneOutput) openMachine ≡ 1ℚ
open-input-marker-test = refl

open-input-extraction : Dmap (decodeReplies {S = openSignature})
    (runFrom (product (wiring (markerEnvironment openSignature)) openMachine
      (markerAutomaton openSignature)) (markedSchedule {S = openSignature} (tt ∷ [])) (tt , tt))
  ≈Mℚ paddedReplyRun openMachine (tt ∷ []) tt
open-input-extraction = marker-extraction openMachine (tt ∷ []) tt

marker-source-distinct : Source.evaluate (markerTest four correlated) alternating
  ≢ Source.evaluate (markerTest four correlated) grouped
marker-source-distinct ()

nonempty-native-codec : Dmap (Information.decode (markerCodec {S = Native.coinSignature bit}))
    (Information.execute (markerInstrumentation Native.real)
      (Information.compileWord (markerInstrumentation Native.real) (false ∷ true ∷ []))
      (initial Native.real))
  ≈Mℚ paddedReplyRun Native.real (false ∷ true ∷ []) (initial Native.real)
nonempty-native-codec = Information.extraction (markerInstrumentation Native.real)
  (false ∷ true ∷ []) (initial Native.real)

linkedSignature : Signature
linkedSignature = productSignature (Native.coinSignature bit) Native.receiverSignature empty

linkedReal linkedIdeal : Automaton linkedSignature
linkedReal = product (wiring Native.echoEnvironment) Native.real Native.receiver
linkedIdeal = product (wiring Native.echoEnvironment) Native.ideal Native.receiver

linkedSimulation : Simulation linkedReal linkedIdeal
linkedSimulation = product-simulation (wiring Native.echoEnvironment)
  Native.masked-simulation (identity-simulation Native.receiver)

linked-padded : ∀ ρ q → paddedReplyRun linkedReal ρ q
  ≈Mℚ paddedReplyRun linkedIdeal ρ (stateMap linkedSimulation q)
linked-padded = simulation-implies-padded linkedSimulation

linkedReply : Maybe (Bool Data.Sum.Base.⊎ Bool) → Bool
linkedReply nothing = false
linkedReply (just (inj₁ b)) = b
linkedReply (just (inj₂ b)) = b

linkedAdaptive : P.Calls (Tick linkedSignature) Bool
linkedAdaptive = P.call (inj₂ tt) tt λ _ → P.call (inj₁ false) tt λ _ →
  P.call (inj₁ true) tt λ reply → P.call (inj₂ tt) tt λ received →
    P.coin uniform-Bool λ b →
      P.ret (if b then linkedReply reply else linkedReply received)

linked-native-results : resourceResult linkedReal none tt linkedAdaptive (initial linkedReal)
  ≈Mℚ resourceResult linkedIdeal none tt linkedAdaptive (initial linkedIdeal)
linked-native-results = padded-implies-resource-calls linkedReal linkedIdeal
  (initial linkedReal) (initial linkedIdeal)
  (λ ρ → linked-padded ρ (initial linkedReal)) none tt linkedAdaptive

linkedConsumer : P.Protocol (Tick linkedSignature) Ωᴵ
linkedConsumer = record
  { St = ⊤ ; init = tt ; step = λ _ _ _ → P.mapᶜ (tt ,_) linkedAdaptive }

linked-composed-results : runᵖ (linkedConsumer P.∘ᵖ resource linkedReal)
  ≈Mℚ runᵖ (linkedConsumer P.∘ᵖ resource linkedIdeal)
linked-composed-results = padded-implies-consumers linkedReal linkedIdeal
  (λ ρ → linked-padded ρ (initial linkedReal)) linkedConsumer

linked-consumer-half : E (runᵖ (linkedConsumer P.∘ᵖ resource linkedReal))
  (maybeℚ (λ where false → 0ℚ ; true → 1ℚ)) ≡ ½
linked-consumer-half = refl

linked-marker-extraction : Dmap (decodeReplies {S = linkedSignature})
    (runFrom (product (wiring (markerEnvironment linkedSignature)) linkedReal (markerAutomaton linkedSignature))
      (markedSchedule {S = linkedSignature} (inj₂ tt ∷ inj₁ false ∷ inj₁ true ∷ inj₂ tt ∷ []))
      (initial linkedReal , tt))
  ≈Mℚ paddedReplyRun linkedReal (inj₂ tt ∷ inj₁ false ∷ inj₁ true ∷ inj₂ tt ∷ []) (initial linkedReal)
linked-marker-extraction = marker-extraction linkedReal
  (inj₂ tt ∷ inj₁ false ∷ inj₁ true ∷ inj₂ tt ∷ []) (initial linkedReal)
