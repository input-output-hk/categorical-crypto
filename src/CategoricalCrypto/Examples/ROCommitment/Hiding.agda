{-# OPTIONS --safe --without-K --guardedness #-}

-- The same hash-based commitment against a corrupted receiver: the ideal
-- functionality, the honest committer and the programming simulator.
--
-- The honest committer takes its bit from the environment on `Honᴵʰ`; the
-- receiver's view (commitment, opening, oracle access) is `Advᴵʰ`.  The real
-- committer draws `r` and publishes `H(b ∷ r)`; the simulator publishes a
-- fresh uniform digest before it knows `b` and, when `F_com` releases the bit,
-- draws `r` and programs that one point to the published digest.  Every other
-- point is relayed to the resource's oracle, so the ideal functionality stays
-- a `wireᴹ` over `Examples.ROCommitment`'s resource (`docs/fcom-hiding.md`).

open import Class.DecEq

open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Function.Base
open import Level
open import Relation.Nullary.Decidable.Core

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.ROCommitment.Hiding (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- Interfaces

-- The environment hears back only a refusal: everything a hiding experiment
-- observes goes through the corrupted receiver.
data HonQʰ : Set where
  commitᴱ : Bool → HonQʰ
  openᴱ   : HonQʰ

data HonAʰ : Set where
  nakᴱ : HonAʰ

Honᴵʰ : Iface
Honᴵʰ = HonAʰ ⇿ HonQʰ

data AdvQʰ : Set where
  askᴿᶜ : Pt → AdvQʰ

data AdvAʰ : Set where
  ansᴿᶜ : Dig → AdvAʰ
  comᴿᶜ : Dig → AdvAʰ
  opnᴿᶜ : Bool → Dig → AdvAʰ

Advᴵʰ : Iface
Advᴵʰ = AdvAʰ ⇿ AdvQʰ

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

data Held : Set where
  freshᴴ : Held
  boundᴴ : Bool → Dig → Held
  shownᴴ : Held

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
realStepʰ (_ , inj₁ _)                 = botₚ
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
stateʰ = initˢ HStʰ (readyʰ freshᴴ)

realʰ : Proc Resᴵ (Advᴵʰ ⊗ᴵ Honᴵʰ)
realʰ = mk stateʰ realStepʰ

------------------------------------------------------------------------
-- The simulator: equivocation by programming

data Progʰ : Set where
  blankᵖ : Progʰ
  pubᵖ   : Dig → Progʰ
  pinᵖ   : Pt → Dig → Progʰ

data SStʰ : Set where
  idleᵖ  : Progʰ → SStʰ
  relayᵖ : Progʰ → SStʰ

pinnedʰ : Progʰ → Pt → Maybe Dig
pinnedʰ (pinᵖ y c) x = case x ≟ y of λ where
  (yes _) → just c
  (no  _) → nothing
pinnedʰ _ _ = nothing

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
stateᵖ = initˢ SStʰ (idleᵖ blankᵖ)

simulatorʰ : Proc Lkᴵʰ Advᴵʰ
simulatorʰ = mk stateᵖ simStepʰ
