{-# OPTIONS --safe --without-K --guardedness #-}

open import Relation.Binary.Definitions using (DecidableEquality)
open import CategoricalCrypto.CSP.Interface

module CategoricalCrypto.CSP.Trace.Testing (Sort : Set) (Payload : Sort → Set)
  (Sort-≟ : DecidableEquality Sort) (Ω : Interface Sort Payload) where

open import Categories.Category.Instance.Setoids
open import Categories.Functor.Presheaf
open import Level using (0ℓ; suc)

open import CategoricalCrypto.CSP.Category Sort Payload
open import CategoricalCrypto.CSP.SemanticInvariance Sort Payload Sort-≟
open import CategoricalCrypto.CSP.Trace.Observation Sort Payload
open import CategoricalCrypto.UC.Core

evaluationᵀ : Evaluation OpenCSP (suc 0ℓ) (suc 0ℓ)
evaluationᵀ = record
  { J = I Sort Payload ; Ω = Ω ; S = trace-setoid (I Sort Payload) Ω
  ; eval = record { to = trace-observations ; cong = λ eq → project-respect (observations-respect eq) } }

ℰᵀ : Presheaf OpenCSP (Setoids (suc 0ℓ) (suc 0ℓ))
ℰᵀ = Observable.ℰᴼ (Evaluation.observable evaluationᵀ)

open Observable (Evaluation.observable evaluationᵀ) public
  using (Test; _≋_; ℰ₀; pull; pull-cong; ≋-isEquivalence; ≋-cast)
  renaming (≈⇒≋ to structural⇒test-equality)
