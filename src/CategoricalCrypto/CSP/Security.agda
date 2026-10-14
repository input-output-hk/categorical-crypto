{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Security where

open import Categories.Category.Core
open import Data.Bool.Base
open import Data.Bool.Properties using (_≟_)
open import Data.Product.Base

open import CategoricalCrypto.CSP.SecurityNetwork
open import CategoricalCrypto.CSP.Category Bool Payload
open import CategoricalCrypto.CSP.Congruence Bool Payload
open import CategoricalCrypto.CSP.Interface Bool Payload
open import CategoricalCrypto.CSP.Interchange Bool Payload
open import CategoricalCrypto.CSP.Network Bool Payload
open import CategoricalCrypto.CSP.Observation Bool Payload
open import CategoricalCrypto.CSP.Plugging Bool Payload
open import CategoricalCrypto.CSP.SemanticInvariance Bool Payload _≟_
import CategoricalCrypto.CSP.Setup as Setup
open import CategoricalCrypto.CSP.Structure Bool Payload
open import CategoricalCrypto.CSP.Testing Bool Payload _≟_ Ω

module Cat = Category OpenCSP
module UC = Setup Bool Payload _≟_ Ω

simulator : ∀ {X′} → Network X X′ → Network Y X′
simulator a = a ∘ h

opaque
  adversarial-flattening : ∀ {X′} (a : Network X X′)
    → ((a ⊗₁ id {B}) ∘ f) ≅ ((simulator a ⊗₁ id {B}) ∘ g)
  adversarial-flattening {X′} a = converter-adversarial-flattening
    {A = I} {X = X} {Y = Y} {X′ = X′} {B = B} f g h flattening a

opaque
  experiments-flatten : real-experiment ≅ ideal-experiment
  experiments-flatten = Cat.∘-resp-≈ʳ flattening

opaque
  experiment-observations : observations real-experiment ≈ᴼ observations ideal-experiment
  experiment-observations = observations-respect experiments-flatten

ideal-verdict-trace : NativeObservation.traces (observations ideal-experiment) verdict-trace
ideal-verdict-trace = proj₁ (_≈ᴼ_.traces experiment-observations verdict-trace) real-verdict-trace

ideal-terminal-refusal : ∀ refusal → NativeObservation.failures (observations ideal-experiment) verdict-trace refusal
ideal-terminal-refusal refusal = proj₁ (_≈ᴼ_.failures experiment-observations verdict-trace refusal)
  (real-terminal-refusal refusal)

contextual-experiments : real-experiment ≋ ideal-experiment
contextual-experiments = structural⇒test-equality experiments-flatten

f≤UCg : UC._≤UC_ {A = I} {X = X} {B = B} {Y = Y} f g
f≤UCg {X′} a = simulator a , UC.≈C⇒≈ᵁ
  {A = I} {X = X′} {B = B}
  {f = (a ⊗₁ id {B}) ∘ f} {g = (simulator a ⊗₁ id {B}) ∘ g}
  (adversarial-flattening a)
