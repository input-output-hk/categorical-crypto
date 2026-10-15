{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.ObservationRefinement (Sort : Set) (Payload : Sort → Set) where

open import Data.Product.Base
open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Observation Sort Payload

-- The raw triple is not divergence flooded. This preorder is not the
-- equality used by CSP.Testing or the U/UC security interfaces.
infix 4 _⊑ᴼ_
record _⊑ᴼ_ {A B : Interface} (spec impl : NativeObservation A B) : Set₁ where
  module S = NativeObservation spec
  module I = NativeObservation impl
  field
    traces : ∀ xs → I.traces xs → S.traces xs
    failures : ∀ xs refusal → I.failures xs refusal → S.failures xs refusal
    divergences : ∀ xs → I.divergences xs → S.divergences xs

reflexive : ∀ {A B} {o : NativeObservation A B} → o ⊑ᴼ o
reflexive = record { traces = λ _ p → p ; failures = λ _ _ p → p ; divergences = λ _ p → p }

transitive : ∀ {A B} {p q r : NativeObservation A B} → p ⊑ᴼ q → q ⊑ᴼ r → p ⊑ᴼ r
transitive first second = record
  { traces = λ xs p → _⊑ᴼ_.traces first xs (_⊑ᴼ_.traces second xs p)
  ; failures = λ xs refusal p → _⊑ᴼ_.failures first xs refusal (_⊑ᴼ_.failures second xs refusal p)
  ; divergences = λ xs p → _⊑ᴼ_.divergences first xs (_⊑ᴼ_.divergences second xs p) }

mutual-equality : ∀ {A B} {p q : NativeObservation A B} → p ⊑ᴼ q → q ⊑ᴼ p → p ≈ᴼ q
mutual-equality forward backward = record
  { traces = λ xs → _⊑ᴼ_.traces backward xs , _⊑ᴼ_.traces forward xs
  ; failures = λ xs refusal → _⊑ᴼ_.failures backward xs refusal , _⊑ᴼ_.failures forward xs refusal
  ; divergences = λ xs → _⊑ᴼ_.divergences backward xs , _⊑ᴼ_.divergences forward xs }
