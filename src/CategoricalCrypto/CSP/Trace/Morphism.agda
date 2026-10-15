{-# OPTIONS --safe --without-K --guardedness #-}

open import Relation.Binary.Definitions using (DecidableEquality)
open import CategoricalCrypto.CSP.Interface

module CategoricalCrypto.CSP.Trace.Morphism (Sort : Set) (Payload : Sort → Set)
  (Sort-≟ : DecidableEquality Sort) (Ω : Interface Sort Payload) where

open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Presheaf.Morphism
open import Categories.NaturalTransformation using (ntHelper)
open import Data.Product.Base
open import Relation.Binary.Bundles using (Setoid)

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.CSP.Category Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
import CategoricalCrypto.CSP.Setup as FullSetup
import CategoricalCrypto.CSP.Testing as FullTesting
import CategoricalCrypto.CSP.Trace.Setup as TraceSetup
open import CategoricalCrypto.CSP.Trace.Observation Sort Payload
import CategoricalCrypto.CSP.Trace.Testing as TraceTesting
open import CategoricalCrypto.UCSetup.Morphism

module Full = FullSetup Sort Payload Sort-≟ Ω
module Trace = TraceSetup Sort Payload Sort-≟ Ω
module FTest = FullTesting Sort Payload Sort-≟ Ω
module TTest = TraceTesting Sort Payload Sort-≟ Ω

consumer-cong : ∀ {A} {t u : FTest.Test A} → t FTest.≋ u → t TTest.≋ u
consumer-cong eq closure = project-respect (eq closure)

consumer-natural : ∀ {A B} (f : Network A B) (t : FTest.Test B)
  → FTest.pull f t TTest.≋ TTest.pull f t
consumer-natural f t = Setoid.refl (TTest.ℰ₀ _)

consumer-map : PresheafMorphism idF FTest.ℰᶜˢᵖ TTest.ℰᵀ
consumer-map = record { ν = ntHelper record
  { η = λ _ → record { to = λ t → t ; cong = consumer-cong }
  ; commute = λ f {t} → consumer-natural f t } }

consumer-map-epi : PresheafMorphism.Epi consumer-map
consumer-map-epi t = t , Setoid.refl (TTest.ℰ₀ _)

fullCSP→traceCSP : UCSetupMorphism Full.StdSetup Trace.StdSetup
fullCSP→traceCSP = changeKernel FTest.ℰᶜˢᵖ TTest.ℰᵀ consumer-map

≈ℰ-preserved : ∀ {A B} {f g : Network A B} → f Full.≈ℰ g → f Trace.≈ℰ g
≈ℰ-preserved {A} {B} {f} {g} eq = Trace.KE.mk∼ λ {t} →
  consumer-cong {A = A} {t = FTest.pull f t} {u = FTest.pull g t}
    (Full.KE.run∼ eq {t})

open Refine Full.StdSetup TTest.ℰᵀ ≈ℰ-preserved public

private variable
  A B X Y X′ : Interface Sort Payload

same-simulator : {f : Network A (Full.T₀ X B)} {g : Network A (Full.T₀ Y B)}
  (a : Network X X′) (s : Network Y X′)
  → Full._≈ᵁ_ {A = A} {X = X′} {B = B}
      (Full.sub a {B} Full.𝒞.∘ f) (Full.sub s {B} Full.𝒞.∘ g)
  → Trace._≈ᵁ_ {A = A} {X = X′} {B = B}
      (Trace.sub a {B} Trace.𝒞.∘ f) (Trace.sub s {B} Trace.𝒞.∘ g)
same-simulator {A = A} {X = X} {B = B} {Y = Y} {X′ = X′} {f = f} {g = g} a s =
  ≈ᵁ-refine {A = A} {X = X′} {B = B}
    {f = Full.sub a {B} Full.𝒞.∘ f} {g = Full.sub s {B} Full.𝒞.∘ g}

-- Refine's order transfer uses the dummy theorem; this version preserves each
-- supplied adversary-specific witness, rather than reconstructing it from the dummy.
≤UC-pointwise : {f : Network A (Full.T₀ X B)} {g : Network A (Full.T₀ Y B)}
  → Full._≤UC_ {A = A} {X = X} {B = B} {Y = Y} f g
  → Trace._≤UC_ {A = A} {X = X} {B = B} {Y = Y} f g
≤UC-pointwise {A = A} {X = X} {B = B} {Y = Y} {f = f} {g = g} le a =
  let s , eq = le a
  in s , same-simulator {A = A} {X = X} {B = B} {Y = Y} {f = f} {g = g} a s eq
