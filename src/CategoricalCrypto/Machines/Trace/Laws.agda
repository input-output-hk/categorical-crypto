{-# OPTIONS --safe --without-K #-}

-- `Machines.Trace.Remaining`, closed: all four laws are theorems, so the record
-- is a term and the only hypothesis left in the machine layer is the base's own
-- iteration (`Machines.Iteration.Elgot`), which `Machines.Base` discharges at
-- `Kl(Dₚ)`.  Building the record is what certifies the four theorems inhabit
-- `Remaining`'s fields rather than lookalikes; the explicit lambdas are there
-- because each field's generalized implicit telescope need not be in the order
-- its proof happens to bind.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
import Categories.Category.Monoidal.Distributive as MD

import CategoricalCrypto.Machines.Iteration as Iteration
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Congruence as Congruence
import CategoricalCrypto.Machines.Trace.Fubini as Fubini
import CategoricalCrypto.Machines.Trace.Superposing as Superposing
import CategoricalCrypto.Machines.Trace.Vanishing as Vanishing

module CategoricalCrypto.Machines.Trace.Laws
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱)
  (E : Iteration.Elgot 𝒱 dist 𝒫) where

open Congruence 𝒱 dist 𝒫 E
open Fubini 𝒱 dist 𝒫 E
open Superposing 𝒱 dist 𝒫 E
open Trace 𝒱 dist 𝒫 E
open Vanishing 𝒱 dist 𝒫 E

Remainingᴹ : Remaining
Remainingᴹ = record
  { trace-resp-≲ = λ s → trace-resp-≲ s
  ; vanishing₂   = λ f → vanishing₂ f
  ; superposing  = λ f → superposing f
  ; trace-comm   = λ f → trace-comm f
  }
