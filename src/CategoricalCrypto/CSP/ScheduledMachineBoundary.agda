{-# OPTIONS --safe --guardedness #-}

-- The obstruction concerns transition-faithful original-interface encodings,
-- not arbitrary functors. A scheduler adds an inhabited input to the interface.
module CategoricalCrypto.CSP.ScheduledMachineBoundary where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base

import CategoricalCrypto.Channel.Core as C
open import CategoricalCrypto.CSP.GlobalClasses
import CategoricalCrypto.CSP.ScheduledBoundary as Source
open import CategoricalCrypto.CSP.ScheduledMachine Bool payload
import CategoricalCrypto.Machine.Core as M
import CategoricalCrypto.Machine.Initialized as I
open import Relation.Nullary using (¬_)

module Atomic = ScheduleMachine (closed receiver)

atomic-communication-and-termination : I.Executes Atomic.initialized
  (Atomic.encode (Three.τ ∷ Three.visible Three.√ ∷ []))
atomic-communication-and-termination = Three.completed ,
  Atomic.preserve-exact Source.atomic-communication-and-termination

opaque
  unfolding C._⊗₀_

  closed-machine-no-input : C.Channel.inType (C.I M.⊗ᵀ C.I) → ⊥
  closed-machine-no-input i = eliminate i
    where
    eliminate : ⊥ ⊎ ⊥ → ⊥
    eliminate (inj₁ ())
    eliminate (inj₂ ())

no-faithful-closed-activation : (machine : M.Machine C.I C.I)
  → ¬ (Σ (M.Machine.State machine) (λ p → Σ (M.Machine.State machine) (λ q →
      Σ (C.Channel.inType (C.I M.⊗ᵀ C.I)) (λ i →
      Σ (Maybe (C.Channel.outType (C.I M.⊗ᵀ C.I))) (λ o →
        M.Machine.stepRel machine p i o q)))))
no-faithful-closed-activation machine (_ , _ , i , _) = closed-machine-no-input i

record ClosedStepEncoder (machine : M.Machine C.I C.I) : Set where
  field state : Three.Configuration → M.Machine.State machine
        preserve : ∀ {p l q} → Three._─[_]→_ p l q
          → Σ (C.Channel.inType (C.I M.⊗ᵀ C.I)) (λ i →
            Σ (Maybe (C.Channel.outType (C.I M.⊗ᵀ C.I))) (λ o →
              M.Machine.stepRel machine (state p) i o (state q)))

no-closed-step-encoder : (machine : M.Machine C.I C.I) → ¬ (ClosedStepEncoder machine)
no-closed-step-encoder machine encoder =
  closed-machine-no-input (proj₁ (ClosedStepEncoder.preserve encoder three-advance-atomically))
