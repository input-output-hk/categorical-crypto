{-# OPTIONS --safe --without-K --guardedness #-}

-- Readout is confined to the existing represented nonempty common-channel
-- family. No correspondence for arbitrary networks or external events is added.
module CategoricalCrypto.CSP.NativeExtensionalHiding (X B : Set) where

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Interface ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Observation ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.ObservationRefinement ⊤ (λ _ → X) using (_⊑ᴼ_)
import CategoricalCrypto.CSP.ExtensionalHiding as Extensional
import CategoricalCrypto.CSP.InfiniteObservation as Infinite
import CategoricalCrypto.CSP.NativeCorrespondence as Common
import CategoricalCrypto.CSP.NativeReadout as Readout

module C = Common X B
module H = Extensional (⊤ × X) B (λ _ → true)
module J = Infinite (⊤ × X) B (λ _ → true)
module M = H.Mask (λ _ → true)
module V = Readout X B
open C using (Nonempty; shape+; Family; fold)

module Admissible (s : Nonempty) (pol : ⟨ shape+ s ⟩ → Polarity)
  (producer listener : ⟨ shape+ s ⟩) (producer-output : pol producer ≡ output)
  (only-producer : ∀ k → pol k ≡ output → k ≡ producer)
  (listener-input : pol listener ≡ input) (distinct : listener ≢ producer) where

  module View (p : Family s) = V.ClosedReadout s pol producer listener producer-output only-producer listener-input distinct p

  readout : ∀ {p q : Family s} → H.RawInclusion (C.O.Hide (λ _ → true) (fold s p)) (C.O.Hide (λ _ → true) (fold s q))
    → observations (View.Q.network p) ⊑ᴼ observations (View.Q.network q)
  readout {p} {q} inclusion = record
    { traces = λ xs path → S.trace-to-network xs (H.RawInclusion.traces inclusion (I.trace-to-native xs path))
    ; failures = λ xs refusal failure → S.failure-to-network xs refusal (H.RawInclusion.failures inclusion (I.failure-to-native xs refusal failure))
    ; divergences = λ xs divergence → S.divergence-to-network xs (H.RawInclusion.divergences inclusion (I.divergence-to-native xs divergence)) }
    where
    module S = View p
    module I = View q

  ranked-refinement : ∀ {p q : Family s} → H.RawInclusion (fold s p) (fold s q) → M.Progress (fold s q)
    → observations (View.Q.network p) ⊑ᴼ observations (View.Q.network q)
  ranked-refinement inclusion progress = readout (M.ranked-hiding inclusion progress)

  residual-refinement : ∀ {p q : Family s} → H.RawInclusion (fold s p) (fold s q)
    → (∀ {xs u} → J.Residual (fold s q) xs u → J.Residual (fold s p) xs u)
    → observations (View.Q.network p) ⊑ᴼ observations (View.Q.network q)
  residual-refinement inclusion residual = readout
    (J.Mask.residual-hiding (λ _ → true) (H.RawInclusion.traces inclusion) (H.RawInclusion.failures inclusion) residual)
