{-# OPTIONS --safe --without-K --guardedness #-}

-- State predicates over machine PRESENTATIONS, and the flag-wire machine that
-- turns a Boolean state test into an interface event
-- (`docs/state-event-contract.md`).
--
-- A predicate lives on one representative's state type.  Machine equality does
-- not transport it: an erased state component gives no descent
-- (`UC.Machine.StateEvent.HitTests.ghost-no-descent`).
--
-- `M ▷ P` samples `P` at the initial state, which may be effectful, and at
-- every COMPLETED ACTIVATION — an answer on `B` — and answers the accumulated
-- flag on one extra `Ωᴵ` port, asked for by a tick.  Reading the flag of a
-- composite is `UC.Machine.StateEvent.Read`.

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Sum.Base hiding (map₁)
open import Data.Unit.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding ([_])

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Machines.Run
open import CategoricalCrypto.UC.Machine

module CategoricalCrypto.UC.Machine.StateEvent where

StateTest : {A B : Iface} → Proc A B → Set
StateTest M = MC.St M → Bool

------------------------------------------------------------------------
-- The flag-wire machine

module _ {A B : Iface} (M : Proc A B) (P : StateTest M) where

  sample : Bool → MC.St M × (Neg A ⊎ Pos B) → (MC.St M × Bool) × (Neg A ⊎ (Pos B ⊎ Bool))
  sample f (s , inj₁ a) = (s , f) , inj₁ a
  sample f (s , inj₂ b) = (s , f ∨ P s) , inj₂ (inj₁ b)

  ▷step : (MC.St M × Bool) × (Pos A ⊎ (Neg B ⊎ ⊤)) → Dₚ ((MC.St M × Bool) × (Neg A ⊎ (Pos B ⊎ Bool)))
  ▷step ((s , f) , inj₁ a)        = mapₚ (sample f) (MC.step M (s , inj₁ a))
  ▷step ((s , f) , inj₂ (inj₁ b)) = mapₚ (sample f) (MC.step M (s , inj₂ b))
  ▷step ((s , f) , inj₂ (inj₂ _)) = returnₚ ((s , f) , inj₂ (inj₂ f))

  ▷state : MC.State
  ▷state = record { obj = MC.St M × Bool ; point = λ x → mapₚ (λ s → s , P s) (MC.point (MC.state M) x) }

  infixl 8 _▷_

  _▷_ : Proc A (B ⊗ᴵ Ωᴵ)
  _▷_ = MC.mk ▷state ▷step
