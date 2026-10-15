{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.TaskPIOA.MarkerTests where

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.TaskPIOA.Adaptive
open import CategoricalCrypto.TaskPIOA.AdaptiveFinite
import CategoricalCrypto.TaskPIOA.AdaptiveTests
open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.Marker
open import CategoricalCrypto.TaskPIOA.Product
import CategoricalCrypto.TaskPIOA.Setup as Source
open import ProbabilisticLogic.Distribution.RationalDist

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

open-input-extraction : Dmap decodeReplies
    (runFrom (product (wiring (markerEnvironment openSignature)) openMachine
      (markerAutomaton openSignature)) (markedSchedule (tt ∷ [])) (tt , tt))
  ≈Mℚ paddedReplyRun openMachine (tt ∷ []) tt
open-input-extraction = marker-extraction openMachine (tt ∷ []) tt
