{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.TaskPIOA.AdaptiveTests where

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation using (runᵖ)
import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.TaskPIOA.Adaptive
open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.Product
open import CategoricalCrypto.TaskPIOA.SSPAdapter
import CategoricalCrypto.TaskPIOA.Setup as Source
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (maybeℚ)

accept : Bool → ℚ
accept false = 0ℚ
accept true = 1ℚ

adaptive-alternating : lookupᴰℚ (entries (nativeExperiment alternating adaptiveCalls))
  (maybeℚ accept) ≡ ½
adaptive-alternating = refl

adaptive-grouped : lookupᴰℚ (entries (nativeExperiment grouped adaptiveCalls))
  (maybeℚ accept) ≡ 0ℚ
adaptive-grouped = refl

padded-alternating : lookupᴰℚ (entries (nativeExperiment alternating paddedCalls))
  (maybeℚ accept) ≡ 1ℚ
padded-alternating = refl

padded-grouped : lookupᴰℚ (entries (nativeExperiment grouped paddedCalls))
  (maybeℚ accept) ≡ 0ℚ
padded-grouped = refl

adaptive-distinguishes : ¬ (nativeExperiment alternating adaptiveCalls
  ≈Mℚ nativeExperiment grouped adaptiveCalls)
adaptive-distinguishes e with e (maybeℚ accept)
... | ()

padded-distinguishes : ¬ (nativeExperiment alternating paddedCalls
  ≈Mℚ nativeExperiment grouped paddedCalls)
padded-distinguishes e with e (maybeℚ accept)
... | ()

not-all-native-consumers : ¬ ((D : P.Protocol (Tick pulseSignature) Ωᴵ)
  → runᵖ (D P.∘ᵖ resource alternating) ≈Mℚ runᵖ (D P.∘ᵖ resource grouped))
not-all-native-consumers all = adaptive-distinguishes (all (nativeConsumer adaptiveCalls))

marker : Automaton pulseSignature
marker = record
  { states = one ; initial = tt ; input = λ ()
  ; choose = λ _ _ → just (inj₁ tt) ; owns = λ _ _ _ _ → refl
  ; kernel = λ _ _ → return-ℚ tt }

markerEnvironment : Environment pulseSignature
markerEnvironment = record
  { signature = pulseSignature ; automaton = marker
  ; wiring = record
    { left = record { name = λ () ; find = λ _ → nothing
                    ; complete = λ () ; sound = λ _ _ () }
    ; right = record { name = λ () ; find = λ _ → nothing
                     ; complete = λ () ; sound = λ _ _ () }
    ; boundary-live = λ () } }

markedSchedule : Schedule (productSignature pulseSignature pulseSignature empty)
markedSchedule = inj₁ tt ∷ inj₂ tt ∷ inj₁ tt ∷ inj₂ tt ∷
  inj₁ tt ∷ inj₂ tt ∷ inj₁ tt ∷ inj₂ tt ∷ []

-- Marker outputs delimit the source activations without changing either
-- automaton. Hence raw fixed-word equivalence is NOT contextual test equality.
markedReward : List (⊤ ⊎ ⊤) → ℚ
markedReward (inj₂ _ ∷ inj₂ _ ∷ inj₁ _ ∷ inj₂ _ ∷ inj₂ _ ∷ []) = 1ℚ
markedReward (inj₂ _ ∷ inj₁ _ ∷ inj₂ _ ∷ inj₂ _ ∷ inj₁ _ ∷ inj₂ _ ∷ []) = 1ℚ
markedReward _ = 0ℚ

markerTest : Source.Test (Source.Syntax.Var pulseSignature)
markerTest = Source.nativeTest markerEnvironment markedSchedule markedReward

source-marker-alternating : Source.evaluate markerTest alternating ≡ 1ℚ
source-marker-alternating = refl

source-marker-grouped : Source.evaluate markerTest grouped ≡ 0ℚ
source-marker-grouped = refl

source-marker-distinguishes : ¬ (Source.evaluate markerTest alternating
  ≡ Source.evaluate markerTest grouped)
source-marker-distinguishes ()
