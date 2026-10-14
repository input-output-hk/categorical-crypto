{-# OPTIONS --safe --without-K --guardedness #-}

open import Relation.Binary.Definitions using (DecidableEquality)
open import CategoricalCrypto.CSP.Interface

module CategoricalCrypto.CSP.Testing (Sort : Set) (Payload : Sort → Set)
  (Sort-≟ : DecidableEquality Sort) (Ω : Interface Sort Payload) where

open import Categories.Category.Instance.Setoids
open import Categories.Functor.Presheaf
open import Level using (0ℓ; suc)

open import CategoricalCrypto.CSP.Category Sort Payload
open import CategoricalCrypto.CSP.Observation Sort Payload
open import CategoricalCrypto.CSP.SemanticInvariance Sort Payload Sort-≟
open import CategoricalCrypto.UC.Core

-- Readouts retain the exact executed trace, not extension-closed FD divergence
-- or chaos after a divergent prefix. No native process quotient is assumed.
evaluationᶜˢᵖ : Evaluation OpenCSP (suc 0ℓ) (suc 0ℓ)
evaluationᶜˢᵖ = record
  { J = I Sort Payload ; Ω = Ω ; S = observation-setoid (I Sort Payload) Ω
  ; eval = record { to = observations ; cong = observations-respect } }

ℰᶜˢᵖ : Presheaf OpenCSP (Setoids (suc 0ℓ) (suc 0ℓ))
ℰᶜˢᵖ = Observable.ℰᴼ (Evaluation.observable evaluationᶜˢᵖ)

open Observable (Evaluation.observable evaluationᶜˢᵖ) public
  using (Test; _≋_; ℰ₀; pull; pull-cong; ≋-isEquivalence; ≋-cast)
  renaming (≈⇒≋ to structural⇒test-equality)
