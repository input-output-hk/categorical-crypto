{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.CSP.Relational (Sort : Set) (Payload : Sort → Set) where

open import Data.Maybe.Base
open import Data.Product.Base
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality

import CategoricalCrypto.Channel.Core as C
open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.ScheduledMachine Sort Payload
open import CategoricalCrypto.CSP.Structure Sort Payload
open import CategoricalCrypto.CSP.Transport Sort Payload
import CategoricalCrypto.CSP.SemanticInvariance as Invariance
import CategoricalCrypto.Machine.Relational as R

interpret : ∀ {A B} (N : Network A B) → R.Initialized C.I (ScheduleMachine.clock N)
interpret N = R.singleton (ScheduleMachine.machine N) (ScheduleMachine.initial-configuration N)

initialized-exact-to : ∀ {A B} (N : Network A B) {ls}
  → Σ (ScheduleMachine.Configuration N) (ScheduleMachine.Exact N (ScheduleMachine.initial-configuration N) ls)
  → R.Executes (interpret N) (ScheduleMachine.encode N ls)
initialized-exact-to N (q , path) =
  ScheduleMachine.initial-configuration N , refl , q , ScheduleMachine.preserve-exact N path

initialized-exact-from : ∀ {A B} (N : Network A B) {ls}
  → R.Executes (interpret N) (ScheduleMachine.encode N ls)
  → Σ (ScheduleMachine.Configuration N) (ScheduleMachine.Exact N (ScheduleMachine.initial-configuration N) ls)
initialized-exact-from N (_ , refl , q , path) = q , ScheduleMachine.reflect-exact N path

transport-respects : ∀ {A B} {F G : Network A B} → OperationalTransport F G
  → interpret F R.≈ᴿ interpret G
transport-respects {F = F} {G} transport = record
  { Related = T.Related
  ; initial-to = λ { refl → _ , refl , T.initial }
  ; initial-from = λ { refl → _ , refl , T.initial }
  ; step-to = forward
  ; step-from = backward }
  where
  module T = OperationalTransport transport
  module F = ScheduleMachine F
  module G = ScheduleMachine G

  forward : ∀ {p q i o p′} → T.Related p q → F.Step p i o p′
    → Σ G.Configuration (λ q′ → G.Step q i o q′ × T.Related p′ q′)
  forward related (F.advance step) =
    let q′ , matched , related′ = T.forward related step
    in q′ , G.advance matched , related′

  backward : ∀ {p q i o q′} → T.Related p q → G.Step q i o q′
    → Σ F.Configuration (λ p′ → F.Step p i o p′ × T.Related p′ q′)
  backward related (G.advance step) =
    let p′ , matched , related′ = T.backward related step
    in p′ , F.advance matched , related′

structural-respects : (Sort-≟ : DecidableEquality Sort) → ∀ {A B} {F G : Network A B}
  → F ≅ G → interpret F R.≈ᴿ interpret G
structural-respects Sort-≟ iso = transport-respects (structural→operational iso)
  where open Invariance Sort Payload Sort-≟
