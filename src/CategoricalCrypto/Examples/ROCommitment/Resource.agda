{-# OPTIONS --safe --without-K --guardedness #-}

-- The resource the two worlds sit on, as a machine: a lazily sampled oracle
-- and the one-shot cell that is `F_com`'s memory.
--
-- `Examples.ROCommitment` fixes only the INTERFACE `Resᴵ`, and the closed
-- games' `Examples.ROCommitment.Oracle` fixes the kernel `fetchT` in `Dist-ℚ`.
-- This is the same kernel in `Dₚ`, where the UC cone's closed runs live: the
-- table is the state, a point already answered is answered again from it, a
-- fresh one draws `uniformₚ k` and is kept.  `Examples.ChimericLedger.POV.oracle` is the
-- same lazy table one layer up, as a `Calls` tree; nothing here is a protocol
-- image, because the system it is plugged under is not one either
-- (`docs/hash-forward.md` item 5).
--
-- Off-protocol activations — a second `putᴿ`, a `getᴿ` before one — are `botₚ`,
-- the layer's honest image of "no behaviour"; neither machine above ever sends
-- them.

open import Class.DecEq

open import Data.Bool.Base using (Bool)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Base using (case_of_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Uniform using (uniformₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.QueryBound using (QB; qb-closed)

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Examples.ROCommitment.Resource (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k

open Core (𝒱ₚ 0ℓ)

-- The table, and the bit the cell is holding.
RState : Set
RState = Tbl × Maybe Bool

resStep : RState × (Pos unitᴵ ⊎ Neg Resᴵ) → Dₚ (RState × (Neg unitᴵ ⊎ Pos Resᴵ))
resStep (_ , inj₁ ())
resStep ((t , m) , inj₂ (hashᴿ x)) = case lookupPt t x of λ where
  (just d) → returnₚ ((t , m) , inj₂ (digᴿ d))
  nothing  → uniformₚ k >>=ₚ λ h → returnₚ (((x , h) ∷ t , m) , inj₂ (digᴿ h))
resStep ((t , m) , inj₂ (putᴿ b))  = case m of λ where
  nothing → returnₚ ((t , just b) , inj₂ rcptᴿ)
  _       → botₚ
resStep ((t , m) , inj₂ getᴿ)      = case m of λ where
  (just b) → returnₚ ((t , just b) , inj₂ (outᴿ b))
  nothing  → botₚ
resStep ((t , m) , inj₂ nakᴿ)      = returnₚ ((t , m) , inj₂ rejᴿ)

stateᵒ : State
stateᵒ = record { obj = RState ; point = λ _ → returnₚ ([] , nothing) ; discard = λ _ → returnₚ tt }

resource : Proc unitᴵ Resᴵ
resource = mk stateᵒ resStep

------------------------------------------------------------------------
-- The kernel, as the game reads it

-- `GamePlaying.Potential.KeepOrSample` in the machine layer's own vocabulary:
-- per oracle query the table either stays put or gains exactly one entry, and
-- the entry it gains is a fresh uniform digest.
hash-hit : (t : Tbl) (m : Maybe Bool) (x : Pt) (d : Dig) → lookupPt t x ≡ just d
         → step resource ((t , m) , inj₂ (hashᴿ x)) ≈ₚ returnₚ ((t , m) , inj₂ (digᴿ d))
hash-hit t m x d eq rewrite eq = ≈ₚ-refl _

hash-miss : (t : Tbl) (m : Maybe Bool) (x : Pt) → lookupPt t x ≡ nothing
          → step resource ((t , m) , inj₂ (hashᴿ x))
            ≈ₚ (uniformₚ k >>=ₚ λ h → returnₚ (((x , h) ∷ t , m) , inj₂ (digᴿ h)))
hash-miss t m x eq rewrite eq = ≈ₚ-refl _

-- …and the cell: the first `putᴿ` receipts and stores, `getᴿ` releases what is
-- stored, `nakᴿ` refuses whatever is.
cell-put : (t : Tbl) (b : Bool)
         → step resource ((t , nothing) , inj₂ (putᴿ b)) ≈ₚ returnₚ ((t , just b) , inj₂ rcptᴿ)
cell-put t b = ≈ₚ-refl _

cell-get : (t : Tbl) (b : Bool)
         → step resource ((t , just b) , inj₂ getᴿ) ≈ₚ returnₚ ((t , just b) , inj₂ (outᴿ b))
cell-get t b = ≈ₚ-refl _

cell-nak : (t : Tbl) (m : Maybe Bool)
         → step resource ((t , m) , inj₂ nakᴿ) ≈ₚ returnₚ ((t , m) , inj₂ rejᴿ)
cell-nak t m = ≈ₚ-refl _

-- A closed process spends no downward query, this one included.
resourceQB : QB 0 resource
resourceQB = qb-closed resource
