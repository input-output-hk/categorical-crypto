{-# OPTIONS --safe --without-K #-}

-- The chimeric UTxO ledger kernel of `talk/slides.typ`, machine-free.
--
-- State is two finite maps — a UTxO set keyed by `(txid , index)` and an
-- account table — and `total` is the invariant preservation-of-value talks
-- about.  A transaction consumes UTxO entries and account balances and creates
-- UTxO entries keyed by `(hash tx , i)`; the hash is the ledger's ONE oracle
-- call per transaction, explicit in `applyTx`'s `Call` result.
--
-- Validation is SEQUENTIAL: inputs are consumed against a shrinking UTxO set
-- and withdrawals debit as they are checked, so a duplicated input or
-- withdrawal cannot create or overdraw value — with per-entry checks against
-- the original state, `POV inputConsuming` would be deterministically false.
--
-- The two variants of the slides are one flag apart: `chimeric` accepts a
-- transaction with no inputs, `inputConsuming` does not.  `Replay` computes why
-- that matters — a no-input transaction can be resubmitted verbatim, its output
-- key collides with the one it created the first time, and since a map union
-- keeps the entry already present the withdrawal is charged twice while only
-- one output exists.  Value is destroyed with probability 1, no hash collision
-- needed.

open import Class.DecEq

open import Data.Bool.Base using (Bool; true; false; not; if_then_else_; _∧_)
open import Data.List.Base using (List; []; _∷_; map; foldl; null)
open import Data.Nat.ListAction using (sum)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just) renaming (map to mapᵐ)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤ᵇ_) renaming (_≡ᵇ_ to _≡ᴺ_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; replicate)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable.Core using (⌊_⌋)

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
  checkIns u (i ∷ is) = found (lookupU u i)
    where found : Maybe TxOut → Maybe (ℕ × Utxo)
          found nothing  = nothing
          found (just o) = mapᵐ (λ vu → proj₂ o + proj₁ vu , proj₂ vu)
                                (checkIns (removeIn i u) is)

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

  -- `ser` serializes a transaction for hashing; its injectivity lives at the
  -- module stating the birthday bound (`ChimericLedger.POV.AtBirthday`).
  module Step (ser : Tx → List Bool) where

    applyTx : Variant → LState → Tx → Call (List Bool) Hash (LState × Bool)
    applyTx vr s@(u , a) tx@(ins , wds , outs) =
      accept (checkIns u ins) (checkWdrls a wds)
      where
        accept : Maybe (ℕ × Utxo) → Maybe Accts → Call (List Bool) Hash (LState × Bool)
        accept (just (vIn , u′)) (just a′) =
          if (vIn + wdrlΣ wds ≡ᴺ valΣ outs) ∧ consumes vr ins
            then callᶜ (ser tx) (λ h → (unionNew u′ (outsAt h 0 outs) , a′) , true)
            else pureᶜ (s , false)
        accept _ _ = pureᶜ (s , false)

------------------------------------------------------------------------
-- The replay attack, computed
------------------------------------------------------------------------

-- One bit of hash is enough: the attack does not need a collision, only the
-- determinism of `hash tx`.
module Replay where

  open Ledger 1
  open Step (λ _ → [])   -- the attack discards the query, so any `ser` will do

  s₀ : LState
  s₀ = [] , (0 , 2) ∷ []

  txᵃ : Tx                                        -- no inputs; move 1 from account 0
  txᵃ = [] , ((0 , 1) ∷ []) , ((1 , 1) ∷ [])

  h : Hash
  h = replicate 1 false

  once twice : LState
  once  = proj₁ (runCall (λ _ → h) (applyTx chimeric s₀ txᵃ))
  twice = proj₁ (runCall (λ _ → h) (applyTx chimeric once txᵃ))

  initial-total : total s₀ ≡ 2
  initial-total = refl

  preserved : total once ≡ 2
  preserved = refl

  destroyed : total twice ≡ 1                     -- a unit of value is gone
  destroyed = refl

  -- The repair rejects the transaction outright, so there is nothing to replay.
  rejected : proj₂ (runCall (λ _ → h) (applyTx inputConsuming s₀ txᵃ)) ≡ false
  rejected = refl
