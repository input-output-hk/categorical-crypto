{-# OPTIONS --safe --without-K --guardedness #-}

-- The same hash-based commitment against a CORRUPTED RECEIVER: the three
-- machines, at an explicitly nontrivial grade.
--
-- The committer is honest now and takes its bit from the environment on
-- `Honᴵʰ`; the receiver is corrupted, so the commitment, the opening and the
-- oracle access it is given are all the adversary-facing `Advᴵʰ`.  The real
-- committer draws `r`, hashes `b ∷ r` and publishes the digest; the simulator
-- publishes a FRESH uniform digest before it knows `b` and, when `F_com`
-- releases the bit, draws `r` and PROGRAMS that one point of the oracle to the
-- digest it already published.
--
-- Programming is an interception, not a second oracle: every other point is
-- relayed to the resource's oracle below, which keeps the ideal functionality
-- a `wireᴹ` — the placement `docs/fcom-extraction.md` fixes and
-- `docs/fcom-hiding.md` re-derives for this half.  The resource, the oracle
-- and the one-shot cell are `Examples.ROCommitment`'s, unchanged; what is new
-- is which side of the cell each party sits on.

open import Class.DecEq

open import Data.Bool.Base using (Bool)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Function.Base using (case_of_)
open import Level using (0ℓ)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Uniform

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒫ₚ)
open import CategoricalCrypto.UC.Machine using (Proc; wireᴹ)

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.ROCommitment.Hiding (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- Interfaces

-- The honest committer's environment-facing port.  The environment drives it
-- and hears back only when it is refused — a second commitment, or an opening
-- with nothing committed.  Everything the experiment observes goes through the
-- corrupted receiver instead, which is what a hiding experiment observes.
data HonQʰ : Set where
  commitᴱ : Bool → HonQʰ
  openᴱ   : HonQʰ

data HonAʰ : Set where
  nakᴱ : HonAʰ

Honᴵʰ : Iface
Honᴵʰ = HonAʰ ⇿ HonQʰ

-- The corrupted receiver's port: oracle access, and the two protocol messages
-- it is sent.
data AdvQʰ : Set where
  askᴿᶜ : Pt → AdvQʰ

data AdvAʰ : Set where
  ansᴿᶜ : Dig → AdvAʰ
  comᴿᶜ : Dig → AdvAʰ
  opnᴿᶜ : Bool → Dig → AdvAʰ

Advᴵʰ : Iface
Advᴵʰ = AdvAʰ ⇿ AdvQʰ

-- The simulator-facing port: the oracle it may relay to, the receipt `F_com`
-- issues at the commitment, and the bit `F_com` releases at the opening.
data LkQʰ : Set where
  relayᶠ : Pt → LkQʰ

data LkAʰ : Set where
  digᶠ  : Dig → LkAʰ
  rcptᶠ : LkAʰ
  bitᶠ  : Bool → LkAʰ

Lkᴵʰ : Iface
Lkᴵʰ = LkAʰ ⇿ LkQʰ

------------------------------------------------------------------------
-- The ideal functionality

-- A WIRE again, and the SAME cell: `putᴿ` takes the environment's bit and
-- receipts the corrupted receiver, `getᴿ` releases it to the receiver, and the
-- cell's refusal is what the environment hears.  The oracle half stays
-- reachable, because the simulator relays every unprogrammed point to it.
downᶠʰ : Neg (Lkᴵʰ ⊗ᴵ Honᴵʰ) → Neg Resᴵ
downᶠʰ (inj₁ (relayᶠ x))  = hashᴿ x
downᶠʰ (inj₂ (commitᴱ b)) = putᴿ b
downᶠʰ (inj₂ openᴱ)       = getᴿ

upᶠʰ : Pos Resᴵ → Pos (Lkᴵʰ ⊗ᴵ Honᴵʰ)
upᶠʰ (digᴿ d) = inj₁ (digᶠ d)
upᶠʰ rcptᴿ    = inj₁ rcptᶠ
upᶠʰ (outᴿ b) = inj₁ (bitᶠ b)
upᶠʰ rejᴿ     = inj₂ nakᴱ

idealʰ : Proc Resᴵ (Lkᴵʰ ⊗ᴵ Honᴵʰ)
idealʰ = wireᴹ upᶠʰ downᶠʰ

------------------------------------------------------------------------
-- The real protocol: the honest committer

-- What the committer holds: nothing, the bit with its opening randomness, or
-- an opening already delivered.
data Held : Set where
  freshᴴ : Held
  boundᴴ : Bool → Dig → Held
  shownᴴ : Held

-- As in `Examples.ROCommitment`, the STATE is split inside each letter's
-- clause; `ownʰ` is the commitment's own hash in flight and `relayʰ` the
-- receiver's.
data HStʰ : Set where
  readyʰ : Held → HStʰ
  ownʰ   : Bool → Dig → HStʰ
  relayʰ : Held → HStʰ

realStepʰ : HStʰ × (Pos Resᴵ ⊎ Neg (Advᴵʰ ⊗ᴵ Honᴵʰ))
          → Dₚ (HStʰ × (Neg Resᴵ ⊎ Pos (Advᴵʰ ⊗ᴵ Honᴵʰ)))
realStepʰ (s , inj₁ (digᴿ d))          = case s of λ where
  (ownʰ b r) → returnₚ (readyʰ (boundᴴ b r) , inj₂ (inj₁ (comᴿᶜ d)))
  (relayʰ h) → returnₚ (readyʰ h            , inj₂ (inj₁ (ansᴿᶜ d)))
  (readyʰ _) → botₚ
realStepʰ (s , inj₁ rcptᴿ)             = botₚ
realStepʰ (s , inj₁ (outᴿ _))          = botₚ
realStepʰ (s , inj₁ rejᴿ)              = botₚ
realStepʰ (s , inj₂ (inj₁ (askᴿᶜ x)))  = case s of λ where
  (readyʰ h) → returnₚ (relayʰ h , inj₁ (hashᴿ x))
  _          → botₚ
realStepʰ (s , inj₂ (inj₂ (commitᴱ b))) = case s of λ where
  (readyʰ freshᴴ) → uniformₚ k >>=ₚ λ r → returnₚ (ownʰ b r , inj₁ (hashᴿ (b ∷ᵛ r)))
  (readyʰ h)      → returnₚ (readyʰ h , inj₂ (inj₂ nakᴱ))
  _               → botₚ
realStepʰ (s , inj₂ (inj₂ openᴱ))       = case s of λ where
  (readyʰ (boundᴴ b r)) → returnₚ (readyʰ shownᴴ , inj₂ (inj₁ (opnᴿᶜ b r)))
  (readyʰ h)            → returnₚ (readyʰ h , inj₂ (inj₂ nakᴱ))
  _                     → botₚ

stateʰ : State
stateʰ = record { obj = HStʰ ; point = λ _ → returnₚ (readyʰ freshᴴ) ; discard = λ _ → returnₚ tt }

realʰ : Proc Resᴵ (Advᴵʰ ⊗ᴵ Honᴵʰ)
realʰ = mk stateʰ realStepʰ

------------------------------------------------------------------------
-- The simulator: equivocation by programming

-- What the programming simulator holds: the fresh digest it published before
-- it knew the bit, and — once `F_com` released the bit — the point it
-- programmed to that digest.
data Progʰ : Set where
  blankᵖ : Progʰ
  pubᵖ   : Dig → Progʰ
  pinᵖ   : Pt → Dig → Progʰ

data SStʰ : Set where
  idleᵖ  : Progʰ → SStʰ
  relayᵖ : Progʰ → SStʰ

-- The digest this query is programmed to, if it is the programmed point.
pinnedʰ : Progʰ → Pt → Maybe Dig
pinnedʰ (pinᵖ y c) x with x ≟ y
... | yes _ = just c
... | no  _ = nothing
pinnedʰ blankᵖ   _ = nothing
pinnedʰ (pubᵖ _) _ = nothing

-- The programmed point is answered from the simulator's own record; every
-- other point goes down to the resource's oracle, which is the only oracle in
-- either world.
serveʰ : Progʰ → Pt → Dₚ (SStʰ × (Neg Lkᴵʰ ⊎ Pos Advᴵʰ))
serveʰ p x = case pinnedʰ p x of λ where
  (just c) → returnₚ (idleᵖ p  , inj₂ (ansᴿᶜ c))
  nothing  → returnₚ (relayᵖ p , inj₁ (relayᶠ x))

simStepʰ : SStʰ × (Pos Lkᴵʰ ⊎ Neg Advᴵʰ) → Dₚ (SStʰ × (Neg Lkᴵʰ ⊎ Pos Advᴵʰ))
simStepʰ (s , inj₁ (digᶠ d)) = case s of λ where
  (relayᵖ p) → returnₚ (idleᵖ p , inj₂ (ansᴿᶜ d))
  (idleᵖ _)  → botₚ
simStepʰ (s , inj₁ rcptᶠ)    = case s of λ where
  (idleᵖ blankᵖ) → uniformₚ k >>=ₚ λ c → returnₚ (idleᵖ (pubᵖ c) , inj₂ (comᴿᶜ c))
  _              → botₚ
simStepʰ (s , inj₁ (bitᶠ b)) = case s of λ where
  (idleᵖ (pubᵖ c)) → uniformₚ k >>=ₚ λ r → returnₚ (idleᵖ (pinᵖ (b ∷ᵛ r) c) , inj₂ (opnᴿᶜ b r))
  _                → botₚ
simStepʰ (s , inj₂ (askᴿᶜ x)) = case s of λ where
  (idleᵖ p) → serveʰ p x
  _         → botₚ

stateᵖ : State
stateᵖ = record { obj = SStʰ ; point = λ _ → returnₚ (idleᵖ blankᵖ) ; discard = λ _ → returnₚ tt }

simulatorʰ : Proc Lkᴵʰ Advᴵʰ
simulatorʰ = mk stateᵖ simStepʰ
