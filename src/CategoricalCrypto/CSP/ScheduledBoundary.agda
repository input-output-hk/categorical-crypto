{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.ScheduledBoundary where

open import Data.Bool.Base
open import Data.List.Base
open import Relation.Nullary using (¬_)

open import CategoricalCrypto.CSP.GlobalClasses
open import CategoricalCrypto.CSP.Scheduled Bool payload

module Atomic = Schedule (closed receiver)
module Stuck = Schedule (closed R.stop)

atomic-communication-and-termination : Atomic.Exact Three.initial-configuration
  (Three.τ ∷ Three.visible Three.√ ∷ []) Three.completed
atomic-communication-and-termination = Atomic.next three-advance-atomically
  (Atomic.next three-joint-completion Atomic.done)

blocked-no-silent-divergence : ¬ (Blocked.Diverges Blocked.initial-configuration)
blocked-no-silent-divergence d = blocked-class-no-silent (Blocked.Diverges.step d)
