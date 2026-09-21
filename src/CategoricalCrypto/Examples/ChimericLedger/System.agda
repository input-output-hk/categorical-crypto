{-# OPTIONS --safe --without-K #-}

-- The chimeric ledger plugged onto a random oracle, as the slides draw it:
--
--     oracle : Protocol unitᴵ HashIf            -- the hash functionality
--     ledger : Protocol HashIf LedgerIf         -- the plain-Agda protocol
--     Sys    = ledger ∘ᵖ oracle                 -- the closed system
--
-- An environment drives `Sys` through `LedgerIf` alone: it submits
-- transactions and asks for audits, and never sees the oracle.  `Sysᴴ` is the
-- same ledger over an arbitrary hash implementation.

open import Class.DecEq

open import Data.Bool.Base
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Function.Base

open import ProbabilisticLogic.Prelude

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Examples.RandomOracle
open import CategoricalCrypto.Iface
open import CategoricalCrypto.OracleCall
open import CategoricalCrypto.Protocol

module CategoricalCrypto.Examples.ChimericLedger.System
  (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) where

open Ledger ℓ
open Step ser

-- One party, hashing BITSTRINGS to ℓ bits: keying the oracle on `Tx` would
-- hide the serialization.
module RO = RandomOracle 1 (List Bool) ℓ

------------------------------------------------------------------------
-- The interfaces and the two components
------------------------------------------------------------------------

data Query : Set where
  submit : Tx → Query
  audit  : Query

data Answer : Set where
  ok      : Bool → Answer
  totalIs : ℕ → Answer

HashIf LedgerIf : Iface
HashIf   = RO.Output ⇿ RO.Input
LedgerIf = Answer ⇿ Query

-- The lazily sampled random oracle: repeats from the table, fresh answers one
-- fair coin per bit (`RandomOracle.step`'s distribution, as a call tree).
oracle : Protocol unitᴵ HashIf
oracle = record { St = RO.Table ; init = [] ; step = go }
  where
    go : RO.Table → RO.Input → Calls unitᴵ (RO.Table × RO.Output)
    go tbl (i , q) = case RO.lookup-bs tbl q of λ where
      (just h) → ret (tbl , (i , h))
      nothing  → uniformVec ℓ λ h → ret ((q , h) ∷ tbl , (i , h))

-- `submit` serializes and calls; `audit` answers purely.  `reCall` tags the
-- query and drops the party index from the reply, `mapCall` wraps the
-- acceptance bit.
ledger : Variant → LState → Protocol HashIf LedgerIf
ledger vr s₀ = record { St = LState ; init = s₀ ; step = go }
  where
    go : LState → Query → Calls HashIf (LState × Answer)
    go s (submit tx) = fromCall (reCall (fzero ,_) proj₂
      (mapCall (λ sb → proj₁ sb , ok (proj₂ sb)) (applyTx vr s tx)))
    go s audit       = ret (s , totalIs (total s))

Sysᴴ : Protocol unitᴵ HashIf → Variant → LState → Protocol unitᴵ LedgerIf
Sysᴴ hash vr s₀ = ledger vr s₀ ∘ᵖ hash

Sys : Variant → LState → Protocol unitᴵ LedgerIf
Sys = Sysᴴ oracle

------------------------------------------------------------------------
-- Where the experiment starts
------------------------------------------------------------------------

-- All the value in ONE UTxO output, keyed by a genesis hash `h₀`: at an
-- account-only genesis the statement is VACUOUS, since `checkIns` rejects
-- every input against an empty UTxO set while `consumes inputConsuming`
-- demands one.  `ChimericLedger.Replay` pins this state's liveness by `refl`.
genesis : Hash → Addr → ℕ → LState
genesis h₀ a V = ((h₀ , 0) , (a , V)) ∷ [] , []

-- The transaction that spends the genesis output, paying the value straight
-- back to the same address: the witness that the experiment runs.
spendGenesis : Hash → Addr → ℕ → Tx
spendGenesis h₀ a V = ((h₀ , 0) ∷ []) , [] , ((a , V) ∷ [])

accepted : Answer → Bool
accepted (ok b)      = b
accepted (totalIs _) = false
