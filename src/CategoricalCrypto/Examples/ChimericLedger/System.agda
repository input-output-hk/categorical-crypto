{-# OPTIONS --safe --without-K #-}

-- The ledger plugged onto a random oracle, `Sys = ledger ∘ᵖ oracle`; `Sysᴴ`
-- is the same ledger over an arbitrary hash implementation.  An environment
-- sees only `LedgerIf`, never the oracle.

open import Class.DecEq

open import Data.Bool.Base
open import Data.Fin.Base using (Fin) renaming (zero to fzero)
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base renaming (_≡ᵇ_ to _≡ᴺ_)
open import Data.Product.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality


open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Examples.RandomOracle
open import CategoricalCrypto.Iface
open import CategoricalCrypto.OracleCall
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe

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

oracle : Protocol unitᴵ HashIf
oracle = RO.Lazy.oracle

submitCall : Call (List Bool) Hash (LState × Bool) → Call (Neg HashIf) (Pos HashIf) (LState × Answer)
submitCall = reCall (fzero ,_) proj₂ ∘ mapCall (λ sb → proj₁ sb , ok (proj₂ sb))

-- At most one oracle call per activation: `UC.QueryBound.qb-oneCall`'s hypothesis.
ledgerCall : Variant → LState → Query → Call (Neg HashIf) (Pos HashIf) (LState × Answer)
ledgerCall vr s (submit tx) = submitCall (applyTx vr s tx)
ledgerCall _  s audit       = pureᶜ (s , totalIs (total s))

ledger : Variant → LState → Protocol HashIf LedgerIf
ledger vr s₀ = record { St = LState ; init = s₀ ; step = λ s q → fromCall (ledgerCall vr s q) }

Sysᴴ : Protocol unitᴵ HashIf → Variant → LState → Protocol unitᴵ LedgerIf
Sysᴴ hash vr s₀ = ledger vr s₀ ∘ᵖ hash

Sys : Variant → LState → Protocol unitᴵ LedgerIf
Sys = Sysᴴ oracle

oracle-repeat : (tbl : RO.Table) (i : Fin 1) (q : List Bool) (h : RO.Out)
              → step oracle ((q , h) ∷ tbl) (i , q) ≡ ret ((q , h) ∷ tbl , (i , h))
oracle-repeat tbl i q h rewrite RO.lookup-bs-here tbl q h = refl

------------------------------------------------------------------------
-- Where the experiment starts
------------------------------------------------------------------------

-- A UTxO genesis, not an account-only one: at the latter the birthday bound
-- is vacuous, since `checkIns` rejects every input against an empty UTxO set
-- while `inputConsuming` demands one (liveness: `Replay.Genesis`).
genesis : Hash → Addr → ℕ → LState
genesis h₀ a V = ((h₀ , 0) , (a , V)) ∷ [] , []

spendGenesis : Hash → Addr → ℕ → Tx
spendGenesis h₀ a V = ((h₀ , 0) ∷ []) , [] , ((a , V) ∷ [])

accepted : Answer → Bool
accepted (ok b)      = b
accepted (totalIs _) = false

ledger-keeps-accts-[] : (vr : Variant) (s : LState) (u : Utxo) (q : Query)
  → AllLeaves (λ sa → proj₂ (proj₁ sa) ≡ []) (step (ledger vr s) (u , []) q)
ledger-keeps-accts-[] _  _ _ audit = refl
ledger-keeps-accts-[] vr _ u (submit (ins , wds , outs))
  with checkIns u ins | checkWdrls [] wds in eq
... | nothing        | _       = refl
... | just _         | nothing = refl
... | just (vIn , _) | just _ with (vIn + wdrlΣ wds ≡ᴺ valΣ outs) ∧ consumes vr ins
...     | false = refl
...     | true  = λ _ → checkWdrls-[] wds eq
