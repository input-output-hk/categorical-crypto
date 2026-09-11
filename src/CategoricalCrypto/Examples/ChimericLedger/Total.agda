{-# OPTIONS --safe --without-K --guardedness #-}

-- The ledger system is live, hence its image plays every strategy to a
-- verdict.
--
-- `UC.Seam.Grounding.UnitGrade` asks for `TotalRun` on both machines, and with
-- good reason: a simulator that never starts makes every ideal invisible, so
-- an emulation with a divergent side says nothing.  For a protocol image the
-- obligation reduces to layer-1 liveness (`totalRun-morphism`), and liveness
-- is structural — neither the oracle nor the ledger writes `dead`, and `_∘ᵖ_`
-- cannot introduce one (`Protocol.Live`).

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Live
  using (NoDeadStep; live; nodead-fromCall; nodead-uniformVec; nodead-∘ᵖ)
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.Protocol.Machine.Total using (TotalRun; totalRun-morphism)

module CategoricalCrypto.Examples.ChimericLedger.Total
  (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) where

open Ledger ℓ

open import CategoricalCrypto.Examples.ChimericLedger.POV ℓ ser

nodead-oracle : NoDeadStep oracle
nodead-oracle tbl (_ , q) with RO.lookup-bs tbl q
... | just _  = tt
... | nothing = nodead-uniformVec ℓ _ λ _ → tt

nodead-ledger : (vr : Variant) (s₀ : LState) → NoDeadStep (ledger vr s₀)
nodead-ledger _ _ _ (submit _) = nodead-fromCall _
nodead-ledger _ _ _ audit      = tt

-- The ledger writes no `dead` whatever it is hashing with, so its liveness is
-- the hash implementation's: `Sys`'s own is the random-oracle instance, and a
-- real hash's is the same statement about its own step trees.
nodead-Sys : (hash : Protocol unitᴵ HashIf) → NoDeadStep hash → (vr : Variant) (s₀ : LState)
           → NoDeadStep (Sysᴴ hash vr s₀)
nodead-Sys hash nd vr s₀ = nodead-∘ᵖ (ledger vr s₀) hash nd (nodead-ledger vr s₀)

totalRun-Sys : (hash : Protocol unitᴵ HashIf) → NoDeadStep hash → (vr : Variant) (s₀ : LState)
             → TotalRun LedgerIf (morphism (Sysᴴ hash vr s₀))
totalRun-Sys hash nd vr s₀ = totalRun-morphism LedgerIf (Sysᴴ hash vr s₀)
                               (live (Sysᴴ hash vr s₀) (nodead-Sys hash nd vr s₀))
