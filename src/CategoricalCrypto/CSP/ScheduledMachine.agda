{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.CSP.ScheduledMachine (Sort : Set) (Payload : Sort → Set) where

open import Data.List.Base
open import Data.Maybe.Base hiding (map)
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Data.Unit.Base
open import Relation.Nullary using (¬_)

import CategoricalCrypto.Channel.Core as C
open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Scheduled Sort Payload
import CategoricalCrypto.Machine.Core as M
import CategoricalCrypto.Machine.Initialized as I

module ScheduleMachine {A B : Interface} (N : Network A B) where
  open Schedule N public

  clock : C.Channel
  clock = Label C.⇿ ⊤

  activate : C.Channel.inType (C.I M.⊗ᵀ clock)
  activate = C.construct-⊗ {A = C.I} {B = clock C.ᵀ} {m = C.In} (inj₂ tt)

  respond : Label → Maybe (C.Channel.outType (C.I M.⊗ᵀ clock))
  respond l = just (C.construct-⊗ {A = C.I} {B = clock C.ᵀ} {m = C.Out} (inj₂ l))

  data Step : M.MachineType C.I clock Configuration where
    advance : ∀ {p l q} → p ─[ l ]→ q → Step p activate (respond l) q

  machine : M.Machine C.I clock
  machine = M.MkMachine Step

  initialized : I.InitializedMachine C.I clock
  initialized = I.initialize machine initial-configuration

  no-unlabelled-response : ∀ {p i q} → ¬ (Step p i nothing q)
  no-unlabelled-response ()

  encode : List Label → List (C.Channel.inType (C.I M.⊗ᵀ clock)
    × Maybe (C.Channel.outType (C.I M.⊗ᵀ clock)))
  encode = map (λ l → activate , respond l)

  preserve-exact : ∀ {p ls q} → Exact p ls q → I.Steps machine p (encode ls) q
  preserve-exact done = I.done
  preserve-exact (next step rest) = I.next (advance step) (preserve-exact rest)

  initialized-preserve : ∀ {ls} → Σ Configuration (Exact initial-configuration ls)
    → I.Executes initialized (encode ls)
  initialized-preserve (q , steps) = q , preserve-exact steps

  record SilentRun (p : Configuration) : Set where
    coinductive
    field next-state : Configuration
          silent-step : Step p activate (respond τ) next-state
          rest : SilentRun next-state

  preserve-divergence : ∀ {p} → Diverges p → SilentRun p
  SilentRun.next-state (preserve-divergence d) = Diverges.next d
  SilentRun.silent-step (preserve-divergence d) = advance (Diverges.step d)
  SilentRun.rest (preserve-divergence d) = preserve-divergence (Diverges.rest d)

  completed-no-activation : ∀ {i o q} → ¬ (Step completed i o q)
  completed-no-activation (advance step) = completed-no-step step

  opaque
    unfolding C._⊗₀_ C.construct-⊗

    reflect-step : ∀ {p l q} → Step p activate (respond l) q → p ─[ l ]→ q
    reflect-step (advance step) = step

    reflect-exact : ∀ {p ls q} → I.Steps machine p (encode ls) q → Exact p ls q
    reflect-exact {ls = []} I.done = done
    reflect-exact {ls = _ ∷ _} (I.next (advance step) rest) = next step (reflect-exact rest)

    initialized-reflect : ∀ {ls} → I.Executes initialized (encode ls)
      → Σ Configuration (Exact initial-configuration ls)
    initialized-reflect (q , steps) = q , reflect-exact steps

    reflect-divergence : ∀ {p} → SilentRun p → Diverges p
    Diverges.next (reflect-divergence d) = SilentRun.next-state d
    Diverges.step (reflect-divergence d) = reflect-step (SilentRun.silent-step d)
    Diverges.rest (reflect-divergence d) = reflect-divergence (SilentRun.rest d)
