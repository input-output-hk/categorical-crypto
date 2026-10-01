{-# OPTIONS --safe --without-K --guardedness #-}

-- Hash-based commitment against a corrupted committer: the ideal
-- functionality, the honest receiver and the extracting simulator.
--
-- The committer is the adversary (port `Advᴵ`); the honest receiver reports on
-- `Honᴵ`.  The receiver relays oracle queries, stores `commitᴬ c`, and at
-- `openᴬ b r` hashes `b ∷ r` and accepts iff the digest is `c`.  The simulator
-- logs every answer it relays and extracts the committed bit from that log.
-- The resource carries both the oracle and `F_com`'s one-bit cell, so the
-- ideal functionality is a stateless `wireᴹ` (`docs/fcom-extraction.md`).  The
-- emulation is approximate; its ε is `Examples.ROCommitment.Game`.

open import Class.DecEq

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
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

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.ROCommitment (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment.Extraction k

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- Interfaces

-- `putᴿ` stores the committed bit and receipts the RECEIVER; `getᴿ` releases
-- it; `nakᴿ` refuses.  The real protocol uses only `hashᴿ`.
data ResQ : Set where
  hashᴿ : Pt → ResQ
  putᴿ  : Bool → ResQ
  getᴿ  : ResQ
  nakᴿ  : ResQ

data ResA : Set where
  digᴿ  : Dig → ResA
  rcptᴿ : ResA
  outᴿ  : Bool → ResA
  rejᴿ  : ResA

Resᴵ : Iface
Resᴵ = ResA ⇿ ResQ

data HonA : Set where
  rcptᴴ    : HonA
  openedᴴ  : Bool → HonA
  refusedᴴ : HonA

Honᴵ : Iface
Honᴵ = HonA ⇿ ⊥

data AdvQ : Set where
  queryᴬ  : Pt → AdvQ
  commitᴬ : Dig → AdvQ
  openᴬ   : Bool → Dig → AdvQ

data AdvA : Set where
  ansᴬ : Dig → AdvA

Advᴵ : Iface
Advᴵ = AdvA ⇿ AdvQ

data LkQ : Set where
  hashˢ   : Pt → LkQ
  commitˢ : Bool → LkQ
  openˢ   : LkQ
  failˢ   : LkQ

data LkA : Set where
  digˢ : Dig → LkA

Lkᴵ : Iface
Lkᴵ = LkA ⇿ LkQ

------------------------------------------------------------------------
-- The ideal functionality

downᶠ : Neg (Lkᴵ ⊗ᴵ Honᴵ) → Neg Resᴵ
downᶠ (inj₁ (hashˢ x))   = hashᴿ x
downᶠ (inj₁ (commitˢ b)) = putᴿ b
downᶠ (inj₁ openˢ)       = getᴿ
downᶠ (inj₁ failˢ)       = nakᴿ

upᶠ : Pos Resᴵ → Pos (Lkᴵ ⊗ᴵ Honᴵ)
upᶠ (digᴿ d) = inj₁ (digˢ d)
upᶠ rcptᴿ    = inj₂ rcptᴴ
upᶠ (outᴿ b) = inj₂ (openedᴴ b)
upᶠ rejᴿ     = inj₂ refusedᴴ

ideal : Proc Resᴵ (Lkᴵ ⊗ᴵ Honᴵ)
ideal = wireᴹ upᶠ downᶠ

------------------------------------------------------------------------
-- The real protocol: the honest receiver

data RSt : Set where
  waitᴿ  : Maybe Dig → RSt
  relayᴿ : Maybe Dig → RSt
  checkᴿ : Dig → Bool → RSt

verdict : Bool → Bool → HonA
verdict b true  = openedᴴ b
verdict b false = refusedᴴ

realStepᵈ : RSt × (Pos Resᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ)) → Maybe (RSt × (Neg Resᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)))
realStepᵈ (s , inj₁ (digᴿ d))          = case s of λ where
  (relayᴿ m)   → just (waitᴿ m          , inj₂ (inj₁ (ansᴬ d)))
  (checkᴿ c b) → just (waitᴿ (just c)   , inj₂ (inj₂ (verdict b ⌊ d ≟ c ⌋)))
  (waitᴿ _)    → nothing
realStepᵈ (s , inj₁ rcptᴿ)             = nothing
realStepᵈ (s , inj₁ (outᴿ _))          = nothing
realStepᵈ (s , inj₁ rejᴿ)              = nothing
realStepᵈ (s , inj₂ (inj₁ (queryᴬ x))) = case s of λ where
  (waitᴿ m) → just (relayᴿ m , inj₁ (hashᴿ x))
  _         → nothing
realStepᵈ (s , inj₂ (inj₁ (commitᴬ c))) = case s of λ where
  (waitᴿ nothing) → just (waitᴿ (just c) , inj₂ (inj₂ rcptᴴ))
  _               → nothing
realStepᵈ (s , inj₂ (inj₁ (openᴬ b r))) = case s of λ where
  (waitᴿ (just c)) → just (checkᴿ c b , inj₁ (hashᴿ (b ∷ᵛ r)))
  _                → nothing
realStepᵈ (s , inj₂ (inj₂ ()))

realStep : RSt × (Pos Resᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ)) → Dₚ (RSt × (Neg Resᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)))
realStep x = detₚ (realStepᵈ x)

stateᴿ : State
stateᴿ = initˢ RSt (waitᴿ nothing)

real : Proc Resᴵ (Advᴵ ⊗ᴵ Honᴵ)
real = mk stateᴿ realStep

------------------------------------------------------------------------
-- The simulator: extraction

data SSt : Set where
  waitˢ  : Tbl → Maybe (Dig × Bool) → SSt
  relayˢ : Pt → Tbl → Maybe (Dig × Bool) → SSt
  checkˢ : Pt → Bool → Tbl → Dig → Bool → SSt

release : Bool → Bool → LkQ
release true  true = openˢ
release _     _    = failˢ

simStep : SSt × (Pos Lkᴵ ⊎ Neg Advᴵ) → Dₚ (SSt × (Neg Lkᴵ ⊎ Pos Advᴵ))
simStep (s , inj₁ (digˢ d))      = case s of λ where
  (relayˢ x L m)     → returnₚ (waitˢ ((x , d) ∷ L) m , inj₂ (ansᴬ d))
  (checkˢ x b L c e) → returnₚ ( waitˢ ((x , d) ∷ L) (just (c , e))
                               , inj₁ (release ⌊ d ≟ c ⌋ (not (b xor e))) )
  (waitˢ _ _)        → botₚ
simStep (s , inj₂ (queryᴬ x))    = case s of λ where
  (waitˢ L m) → returnₚ (relayˢ x L m , inj₁ (hashˢ x))
  _           → botₚ
simStep (s , inj₂ (commitᴬ c))   = case s of λ where
  (waitˢ L nothing) → returnₚ ( waitˢ L (just (c , extract c L))
                              , inj₁ (commitˢ (extract c L)) )
  _                 → botₚ
simStep (s , inj₂ (openᴬ b r))   = case s of λ where
  (waitˢ L (just (c , e))) → returnₚ (checkˢ (b ∷ᵛ r) b L c e , inj₁ (hashˢ (b ∷ᵛ r)))
  _                        → botₚ

stateˢ : State
stateˢ = initˢ SSt (waitˢ [] nothing)

simulator : Proc Lkᴵ Advᴵ
simulator = mk stateˢ simStep
