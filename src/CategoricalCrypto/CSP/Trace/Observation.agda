{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Trace.Observation (Sort : Set) (Payload : Sort → Set) where

open import Data.List.Base
open import Data.Product.Base
open import Level using (0ℓ; suc)
open import Relation.Binary.Bundles using (Setoid)

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Observation Sort Payload
open import CategoricalCrypto.CSP.Operational Sort Payload

TraceObservation : Interface → Interface → Set₁
TraceObservation A B = List (Labels.Visible A B) → Set

infix 4 _≈ᵀ_
record _≈ᵀ_ {A B : Interface} (x y : TraceObservation A B) : Set₁ where
  field traces : ∀ xs → (x xs → y xs) × (y xs → x xs)

trace-setoid : ∀ A B → Setoid (suc 0ℓ) (suc 0ℓ)
trace-setoid A B = record
  { Carrier = TraceObservation A B ; _≈_ = _≈ᵀ_
  ; isEquivalence = record
    { refl = record { traces = λ _ → (λ x → x) , (λ x → x) }
    ; sym = λ eq → record { traces = λ xs → swap (_≈ᵀ_.traces eq xs) }
    ; trans = λ first second → record { traces = λ xs →
      (λ x → proj₁ (_≈ᵀ_.traces second xs) (proj₁ (_≈ᵀ_.traces first xs) x)) ,
      (λ z → proj₂ (_≈ᵀ_.traces first xs) (proj₂ (_≈ᵀ_.traces second xs) z)) } } }

project : ∀ {A B} → NativeObservation A B → TraceObservation A B
project = NativeObservation.traces

project-respect : ∀ {A B} {x y : NativeObservation A B} → x ≈ᴼ y → project x ≈ᵀ project y
project-respect eq = record { traces = _≈ᴼ_.traces eq }

trace-observations : ∀ {A B} → Network A B → TraceObservation A B
trace-observations N = project (observations N)
