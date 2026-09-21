{-# OPTIONS --safe --without-K #-}

-- The chimeric UTxO ledger kernel of `talk/slides.typ`, machine-free.
--
-- State is two finite maps — a UTxO set keyed by `(txid , index)` and an
-- account table — and `total` is the invariant preservation of value talks
-- about.  A transaction consumes UTxO entries and account balances and creates
-- UTxO entries keyed by `(hash tx , i)`; that hash is the ledger's ONE oracle
-- call per transaction, explicit in `applyTx`'s `Call` result.
--
-- The two variants of the slides are one flag apart: `chimeric` accepts a
-- transaction with no inputs, `inputConsuming` does not.  Why that matters is
-- computed in `ChimericLedger.Replay`.

open import Class.DecEq

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_; map; foldl; null)
open import Data.Maybe.Base renaming (map to mapᵐ)
open import Data.Nat.Base renaming (_≡ᵇ_ to _≡ᴺ_)
open import Data.Nat.ListAction
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec)
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core

open import CategoricalCrypto.OracleCall

module CategoricalCrypto.Examples.ChimericLedger where

-- `DecEq-×` is not an upstream instance (it competes with the `--with-K`
-- `DecEq-Σ`); register it, as `categorical-crypto.Prelude` does.
private instance DecEq-×′ = DecEq-×

-- Which transactions the ledger accepts.  `chimeric` is the slides' broken
-- variant; `inputConsuming` is the repair.
data Variant : Set where
  chimeric inputConsuming : Variant

module Ledger (ℓ : ℕ) where

  Hash  = Vec Bool ℓ
  Addr  = ℕ
  TxIn  = Hash × ℕ
  TxOut = Addr × ℕ

  -- `(ins , wdrls , outs)`
  Tx = List TxIn × List (Addr × ℕ) × List TxOut

  Utxo   = List (TxIn × TxOut)
  Accts  = List (Addr × ℕ)
  LState = Utxo × Accts

  ------------------------------------------------------------------------
  -- The two finite maps
  ------------------------------------------------------------------------

  lookupU : Utxo → TxIn → Maybe TxOut
  lookupU []            _ = nothing
  lookupU ((k , v) ∷ m) i = if ⌊ i ≟ k ⌋ then just v else lookupU m i

  removeIn : TxIn → Utxo → Utxo
  removeIn _ []            = []
  removeIn i ((k , v) ∷ m) = if ⌊ i ≟ k ⌋ then m else (k , v) ∷ removeIn i m

  -- Union favouring the entry already present.  This is what swallows a
  -- replayed transaction's output.
  insertNew : Utxo → TxIn × TxOut → Utxo
  insertNew u (k , v) = if is-just (lookupU u k) then u else (k , v) ∷ u

  unionNew : Utxo → Utxo → Utxo
  unionNew = foldl insertNew

  acctOf : Accts → Addr → ℕ
  acctOf []            _ = 0
  acctOf ((y , w) ∷ a) x = if ⌊ x ≟ y ⌋ then w else acctOf a x

  subOne : Addr → ℕ → Accts → Accts
  subOne _ _ []            = []
  subOne x v ((y , w) ∷ a) =
    if ⌊ x ≟ y ⌋ then (y , w ∸ v) ∷ a else (y , w) ∷ subOne x v a

  ------------------------------------------------------------------------
  -- Value
  ------------------------------------------------------------------------

  balance : Utxo → ℕ
  balance u = sum (map (proj₂ ∘ proj₂) u)

  acctΣ : Accts → ℕ
  acctΣ a = sum (map proj₂ a)

  total : LState → ℕ
  total (u , a) = balance u + acctΣ a

  valΣ : List TxOut → ℕ
  valΣ os = sum (map proj₂ os)

  wdrlΣ : List (Addr × ℕ) → ℕ
  wdrlΣ ws = sum (map proj₂ ws)

  ------------------------------------------------------------------------
  -- The step rule: sequential validation
  ------------------------------------------------------------------------

  -- Consume the inputs one at a time against the REMAINING set: a duplicate
  -- fails its lookup.  Returns the value consumed and the surviving UTxO set.
  checkIns : Utxo → List TxIn → Maybe (ℕ × Utxo)
  checkIns u []       = just (0 , u)
  checkIns u (i ∷ is) = case lookupU u i of λ where
    nothing  → nothing
    (just o) → mapᵐ (λ vu → proj₂ o + proj₁ vu , proj₂ vu) (checkIns (removeIn i u) is)

  -- Debit the withdrawals one at a time: each is checked against the
  -- already-debited accounts, so the debit is always exact.
  checkWdrls : Accts → List (Addr × ℕ) → Maybe Accts
  checkWdrls a []             = just a
  checkWdrls a ((x , v) ∷ ws) =
    if v ≤ᵇ acctOf a x then checkWdrls (subOne x v a) ws else nothing

  consumes : Variant → List TxIn → Bool
  consumes chimeric       _   = true
  consumes inputConsuming ins = not (null ins)

  -- The new UTxO entries a transaction creates, keyed by its hash.
  outsAt : Hash → ℕ → List TxOut → Utxo
  outsAt _ _ []       = []
  outsAt h i (o ∷ os) = ((h , i) , o) ∷ outsAt h (suc i) os

  -- `ser` serializes a transaction for hashing; its injectivity is assumed
  -- where the birthday bound is proved (`ChimericLedger.Birthday`).
  module Step (ser : Tx → List Bool) where

    applyTx : Variant → LState → Tx → Call (List Bool) Hash (LState × Bool)
    applyTx vr s@(u , a) tx@(ins , wds , outs) =
      case checkIns u ins , checkWdrls a wds of λ where
        (just (vIn , u′) , just a′) →
          if (vIn + wdrlΣ wds ≡ᴺ valΣ outs) ∧ consumes vr ins
            then callᶜ (ser tx) (λ h → (unionNew u′ (outsAt h 0 outs) , a′) , true)
            else pureᶜ (s , false)
        _ → pureᶜ (s , false)
