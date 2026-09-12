{-# OPTIONS --safe --without-K --guardedness #-}

-- The resource the toy sits on, as a machine: the one-message channel and the
-- hash oracle, at a hash function given as a parameter.
--
-- `Examples.HashForward` fixes only the interface `Resᴵ`, and its emulation is
-- exact for EVERY closure — which is stronger than fixing one, and is why no
-- concrete resource was needed for it (`docs/hash-forward.md` item 4).  What
-- needs one is the probability statement: `UC.Seam.Audit.Context.extractᵍ`
-- bounds the run of a CLOSED system, so something has to be below.
--
-- The oracle is deterministic here, and that is forced rather than chosen:
-- `Dig` is an abstract parameter of the toy, so there is no uniform
-- distribution on it to sample from.  `Examples.ROCommitment.Resource` is the
-- lazily sampled one, at concrete bit vectors.

open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Base using (case_of_)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.QueryBound using (QB; qb-closed)

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Examples.HashForward.Resource
  (Msg Dig : Set) (hash : Msg → Dig) where

open import CategoricalCrypto.Examples.HashForward Msg Dig

open Core (𝒱ₚ 0ℓ)

resStep : Maybe Msg × (Pos unitᴵ ⊎ Neg Resᴵ) → Dₚ (Maybe Msg × (Neg unitᴵ ⊎ Pos Resᴵ))
resStep (_ , inj₁ ())
resStep (_ , inj₂ (putᴿ m))  = returnₚ (just m , inj₂ ackᴿ)
resStep (s , inj₂ getᴿ)      = case s of λ where
  (just m) → returnₚ (just m , inj₂ (gotᴿ m))
  nothing  → botₚ
resStep (s , inj₂ leakᴿ)     = case s of λ where
  (just m) → returnₚ (just m , inj₂ (lkᴿ m))
  nothing  → botₚ
resStep (s , inj₂ (hashᴿ m)) = returnₚ (s , inj₂ (digᴿ (hash m)))

stateᵒ : State
stateᵒ = record { obj = Maybe Msg ; point = λ _ → returnₚ nothing ; discard = λ _ → returnₚ tt }

resource : Proc unitᴵ Resᴵ
resource = mk stateᵒ resStep

------------------------------------------------------------------------
-- The kernel

-- The channel stores, delivers and leaks the same message, and the oracle
-- answers `hash`.  Read off the step, which is what a statement about the
-- closed run reduces to.
put-ack : (s : Maybe Msg) (m : Msg)
        → step resource (s , inj₂ (putᴿ m)) ≈ₚ returnₚ (just m , inj₂ ackᴿ)
put-ack s m = ≈ₚ-refl _

get-msg : (m : Msg) → step resource (just m , inj₂ getᴿ) ≈ₚ returnₚ (just m , inj₂ (gotᴿ m))
get-msg m = ≈ₚ-refl _

leak-msg : (m : Msg) → step resource (just m , inj₂ leakᴿ) ≈ₚ returnₚ (just m , inj₂ (lkᴿ m))
leak-msg m = ≈ₚ-refl _

hash-dig : (s : Maybe Msg) (m : Msg)
         → step resource (s , inj₂ (hashᴿ m)) ≈ₚ returnₚ (s , inj₂ (digᴿ (hash m)))
hash-dig s m = ≈ₚ-refl _

resourceQB : QB 0 resource
resourceQB = qb-closed resource
