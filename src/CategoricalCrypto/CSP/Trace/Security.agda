{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Trace.Security where

open import Data.Bool.Base
open import Data.Bool.Properties using (_≟_)
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.CSP.SecurityNetwork
import CategoricalCrypto.CSP.Security as Source
open import CategoricalCrypto.CSP.Interface Bool Payload
open import CategoricalCrypto.CSP.Network Bool Payload
open import CategoricalCrypto.CSP.Plugging Bool Payload
open import CategoricalCrypto.CSP.Trace.Morphism Bool Payload _≟_ Ω
open import CategoricalCrypto.CSP.Trace.Observation Bool Payload
import CategoricalCrypto.CSP.Trace.Setup as Setup
open import CategoricalCrypto.CSP.Trace.Testing Bool Payload _≟_ Ω
open import CategoricalCrypto.UC.Core using (Evaluation)

module UC = Setup Bool Payload _≟_ Ω

f≤UCg : UC._≤UC_ {A = I} {X = X} {B = B} {Y = Y} f g
f≤UCg = ≤UC-refine {A = I} {X = X} {B = B} {Y = Y} {f = f} {g = g} Source.f≤UCg

f≤UCg-same-simulator : UC._≤UC_ {A = I} {X = X} {B = B} {Y = Y} f g
f≤UCg-same-simulator = ≤UC-pointwise {A = I} {X = X} {B = B} {Y = Y} {f = f} {g = g} Source.f≤UCg

concrete-simulator : ∀ {X′} (a : Network X X′) → proj₁ (f≤UCg-same-simulator a) ≡ a ∘ h
concrete-simulator a = refl

real-verdict : Evaluation.read evaluationᵀ real-experiment verdict-trace
real-verdict = real-verdict-trace

ideal-verdict : Evaluation.read evaluationᵀ ideal-experiment verdict-trace
ideal-verdict = Source.ideal-verdict-trace

experiment-traces : Evaluation.read evaluationᵀ real-experiment ≈ᵀ Evaluation.read evaluationᵀ ideal-experiment
experiment-traces = project-respect Source.experiment-observations
