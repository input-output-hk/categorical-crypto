{-# OPTIONS --safe --without-K --guardedness #-}

-- Raw exact traces, stable failures, and divergence after the exact trace.
-- √ is visible; completion is unstable until consumed. There is no flooding.
module CategoricalCrypto.CSP.Observation (Sort : Set) (Payload : Sort → Set) where

open import Data.List.Base
open import Data.Product.Base
open import Level using (0ℓ; suc)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Nullary using (¬_)

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Operational Sort Payload

module Observe {A B : Interface} (N : Network A B) where
  open Execution N

  private variable
    p q r : Configuration
    xs : List Visible
    e : Visible

  data Executes : Configuration → List Visible → Configuration → Set where
    done : Executes p [] p
    silent-step : p ─[ τ ]→ q → Executes q xs r → Executes p xs r
    visible-step : p ─[ visible e ]→ q → Executes q xs r → Executes p (e ∷ xs) r

  Trace : Configuration → List Visible → Set
  Trace p xs = Σ Configuration (Executes p xs)

  Stable : Configuration → Set
  Stable p = (∀ q → ¬ (p ─[ τ ]→ q)) × (∀ q → ¬ (p ─[ visible √ ]→ q))

  Refuses : Configuration → (Visible → Set) → Set
  Refuses p refusal = Stable p × (∀ e → refusal e → ∀ q → ¬ (p ─[ visible e ]→ q))

  Failure : Configuration → List Visible → (Visible → Set) → Set
  Failure p xs refusal = Σ Configuration (λ q → Executes p xs q × Refuses q refusal)

  Divergence : Configuration → List Visible → Set
  Divergence p xs = Σ Configuration (λ q → Executes p xs q × Diverges q)

  completed-stable : Stable completed
  completed-stable = (λ _ → completed-no-step) , (λ _ → completed-no-step)

  completed-refuses : ∀ refusal → Refuses completed refusal
  completed-refuses refusal = completed-stable , (λ _ _ _ → completed-no-step)

  ready-not-stable : ∀ {q} → (k : Box) → AllRet q → ¬ (Stable (running q))
  ready-not-stable k ready (_ , no√) = no√ completed (finish k ready)

record NativeObservation (A B : Interface) : Set₁ where
  open Labels A B
  field
    traces : List Visible → Set
    failures : List Visible → (Visible → Set) → Set
    divergences : List Visible → Set

record _≈ᴼ_ {A B : Interface} (x y : NativeObservation A B) : Set₁ where
  module X = NativeObservation x
  module Y = NativeObservation y
  field
    traces : ∀ xs → (X.traces xs → Y.traces xs) × (Y.traces xs → X.traces xs)
    failures : ∀ xs refusal → (X.failures xs refusal → Y.failures xs refusal)
      × (Y.failures xs refusal → X.failures xs refusal)
    divergences : ∀ xs → (X.divergences xs → Y.divergences xs) × (Y.divergences xs → X.divergences xs)

observation-setoid : ∀ A B → Setoid (suc 0ℓ) (suc 0ℓ)
observation-setoid A B = record
  { Carrier = NativeObservation A B ; _≈_ = _≈ᴼ_
  ; isEquivalence = record
    { refl = record
      { traces = λ _ → (λ x → x) , (λ x → x)
      ; failures = λ _ _ → (λ x → x) , (λ x → x)
      ; divergences = λ _ → (λ x → x) , (λ x → x) }
    ; sym = λ eq → record
      { traces = λ xs → swap (_≈ᴼ_.traces eq xs)
      ; failures = λ xs refusal → swap (_≈ᴼ_.failures eq xs refusal)
      ; divergences = λ xs → swap (_≈ᴼ_.divergences eq xs) }
    ; trans = λ first second → record
      { traces = λ xs → compose (_≈ᴼ_.traces first xs) (_≈ᴼ_.traces second xs)
      ; failures = λ xs refusal → compose (_≈ᴼ_.failures first xs refusal) (_≈ᴼ_.failures second xs refusal)
      ; divergences = λ xs → compose (_≈ᴼ_.divergences first xs) (_≈ᴼ_.divergences second xs) } } }
  where
  compose : ∀ {X Y Z : Set} → ((X → Y) × (Y → X)) → ((Y → Z) × (Z → Y)) → (X → Z) × (Z → X)
  compose (f , g) (h , k) = (λ x → h (f x)) , (λ z → g (k z))

observations : ∀ {A B} → Network A B → NativeObservation A B
observations N = record
  { traces = O.Trace E.initial-configuration
  ; failures = O.Failure E.initial-configuration
  ; divergences = O.Divergence E.initial-configuration }
  where
  module E = Execution N
  module O = Observe N
