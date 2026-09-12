{-# OPTIONS --safe --without-K --guardedness #-}

-- Hash-based commitment against a CORRUPTED COMMITTER: the three machines, at
-- an explicitly nontrivial grade.
--
-- The committer is the adversary, so its messages and its oracle queries come
-- from the adversary-facing port `Advᴵ`; the receiver is honest and its
-- reactions are the environment-facing `Honᴵ`.  The real protocol is the
-- receiver: it relays the adversary's oracle queries, takes `commitᴬ c` on
-- trust, and at `openᴬ b r` hashes `b ∷ r` itself and accepts iff the digest is
-- the one it stored.  The simulator RECORDS every answer it relays and reads
-- the committed bit off that log at `commitᴬ`.
--
-- The resource below carries BOTH the oracle and the ideal functionality's one
-- bit of memory, so the ideal functionality is a stateless relabelling
-- (`wireᴹ`) exactly as in `Examples.HashForward` — `docs/fcom-extraction.md`
-- records why, and what a stateful ideal would have cost.  Unlike that toy the
-- emulation here is APPROXIMATE: `real` is NOT `subᴵ simulator ∘ ideal`, and
-- the price of the difference is `Examples.ROCommitment.Game`.

open import Class.DecEq

open import Data.Bool.Base using (Bool; false; true; not; _xor_)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Function.Base using (case_of_)
open import Level using (0ℓ)
open import Relation.Nullary.Decidable.Core using (⌊_⌋)

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒫ₚ)
open import CategoricalCrypto.UC.Machine using (Proc; wireᴹ)

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.ROCommitment (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment.Extraction k

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- Interfaces

-- The resource below: the random oracle, and the one-shot cell that is the
-- ideal functionality's memory.  `putᴿ` stores the committed bit and receipts
-- the RECEIVER; `getᴿ` releases it; `nakᴿ` refuses.  The real protocol uses
-- only the oracle half.
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

-- The honest receiver's environment-facing port.  It carries no queries: the
-- receiver never answers the environment, it reports to it.
data HonA : Set where
  rcptᴴ    : HonA
  openedᴴ  : Bool → HonA
  refusedᴴ : HonA

Honᴵ : Iface
Honᴵ = HonA ⇿ ⊥

-- The REAL adversary-facing port: the corrupted committer's oracle access and
-- its two protocol messages.
data AdvQ : Set where
  queryᴬ  : Pt → AdvQ
  commitᴬ : Dig → AdvQ
  openᴬ   : Bool → Dig → AdvQ

data AdvA : Set where
  ansᴬ : Dig → AdvA

Advᴵ : Iface
Advᴵ = AdvA ⇿ AdvQ

-- The IDEAL simulator-facing port: the oracle relayed, and the three things
-- the functionality can be told.  Only the oracle answers back.
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

-- A WIRE: the resource's ports relabelled onto the simulator's and the
-- receiver's.  Its memory is the cell's, which is where a commitment
-- functionality's memory belongs, and its statelessness is what keeps
-- `subᴵ simulator ∘ ideal` free of a ⊕-trace (`UC.Machine.Wire.∘-wireᴹ`).
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

-- Three states: idle with whatever commitment has arrived, an adversary oracle
-- query in flight, and an opening check in flight (the stored digest and the
-- claimed bit).  As in `Examples.HashForward`, the STATE is split inside each
-- letter's clause.
data RSt : Set where
  waitᴿ  : Maybe Dig → RSt
  relayᴿ : Maybe Dig → RSt
  checkᴿ : Dig → Bool → RSt

verdict : Bool → Bool → HonA
verdict b true  = openedᴴ b
verdict b false = refusedᴴ

realStep : RSt × (Pos Resᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ))
         → Dₚ (RSt × (Neg Resᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)))
realStep (s , inj₁ (digᴿ d))          = case s of λ where
  (relayᴿ m)   → returnₚ (waitᴿ m          , inj₂ (inj₁ (ansᴬ d)))
  (checkᴿ c b) → returnₚ (waitᴿ (just c)   , inj₂ (inj₂ (verdict b ⌊ d ≟ c ⌋)))
  (waitᴿ _)    → botₚ
realStep (s , inj₁ rcptᴿ)             = botₚ
realStep (s , inj₁ (outᴿ _))          = botₚ
realStep (s , inj₁ rejᴿ)              = botₚ
realStep (s , inj₂ (inj₁ (queryᴬ x))) = case s of λ where
  (waitᴿ m) → returnₚ (relayᴿ m , inj₁ (hashᴿ x))
  _         → botₚ
realStep (s , inj₂ (inj₁ (commitᴬ c))) = case s of λ where
  (waitᴿ nothing) → returnₚ (waitᴿ (just c) , inj₂ (inj₂ rcptᴴ))
  _               → botₚ
realStep (s , inj₂ (inj₁ (openᴬ b r))) = case s of λ where
  (waitᴿ (just c)) → returnₚ (checkᴿ c b , inj₁ (hashᴿ (b ∷ᵛ r)))
  _                → botₚ
realStep (s , inj₂ (inj₂ ()))

stateᴿ : State
stateᴿ = record { obj = RSt ; point = λ _ → returnₚ (waitᴿ nothing) ; discard = λ _ → returnₚ tt }

real : Proc Resᴵ (Advᴵ ⊗ᴵ Honᴵ)
real = mk stateᴿ realStep

------------------------------------------------------------------------
-- The simulator: extraction

-- It runs the receiver's program against the ideal functionality instead of
-- against the oracle, and keeps the LOG the receiver has no use for.  At
-- `commitᴬ c` the log's unique preimage of `c` supplies the bit the ideal
-- functionality is committed to; at `openᴬ b r` the oracle decides the digest
-- and the extraction decides the bit, and the functionality is told to open
-- only when both agree.
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
stateˢ = record { obj = SSt ; point = λ _ → returnₚ (waitˢ [] nothing) ; discard = λ _ → returnₚ tt }

simulator : Proc Lkᴵ Advᴵ
simulator = mk stateˢ simStep
