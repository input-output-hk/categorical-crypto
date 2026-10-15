{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.NativeFamilyObservation (X B : Set) where

open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Interface ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Observation ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.ObservationRefinement ⊤ (λ _ → X) using (_⊑ᴼ_; mutual-equality)
import CategoricalCrypto.CSP.NativeFamilyRefinement as FamilyRefinement
import CategoricalCrypto.CSP.NativeReadout as Readout

module F = FamilyRefinement X B
module C = F.C
module R = F.N.R
module V = Readout X B
open C using (Nonempty; shape+; Family)
open R using (_⊑_)

module Admissible (s : Nonempty) (pol : ⟨ shape+ s ⟩ → Polarity)
  (producer listener : ⟨ shape+ s ⟩) (producer-output : pol producer ≡ output)
  (only-producer : ∀ k → pol k ≡ output → k ≡ producer)
  (listener-input : pol listener ≡ input) (distinct : listener ≢ producer) where

  module Closed (p : Family s) = C.Closed s pol producer listener producer-output only-producer listener-input distinct p
  module View (p : Family s) = V.ClosedReadout s pol producer listener producer-output only-producer listener-input distinct p

  refinement : ∀ {p q : Family s} → (∀ k → p k ⊑ q k)
    → observations (Closed.network p) ⊑ᴼ observations (Closed.network q)
  refinement {p} {q} pointwise = record
    { traces = λ xs path → S.trace-to-network xs (R.traces {p = S.Q.native p} {q = I.Q.native q} native (I.trace-to-native xs path))
    ; failures = λ xs refusal failure → S.failure-to-network xs refusal (R.failures {p = S.Q.native p} {q = I.Q.native q} native (I.failure-to-native xs refusal failure))
    ; divergences = λ xs divergence → S.divergence-to-network xs (R.divergences {p = S.Q.native p} {q = I.Q.native q} native (I.divergence-to-native xs divergence)) }
    where
    module S = View p
    module I = View q
    native : S.Q.native p ⊑ I.Q.native q
    native = F.hidden-family s pointwise

  mutual-observations : ∀ {p q : Family s} → (∀ k → p k ⊑ q k) → (∀ k → q k ⊑ p k)
    → observations (Closed.network p) ≈ᴼ observations (Closed.network q)
  mutual-observations forward backward = mutual-equality (refinement forward) (refinement backward)
