{-# OPTIONS --safe --without-K #-}

-- The chimeric variant destroys value, computed: everything below holds by
-- `refl` at 1-bit hashes, oracle sampling and ℚ arithmetic included.
--
-- The attack needs no hash collision, only the determinism of `hash tx`.  A
-- transaction with no inputs can be resubmitted verbatim; its output key
-- collides with the one it created the first time, and since `unionNew` keeps
-- the entry already present the withdrawal is charged twice while only one
-- output exists.  `inputConsuming` rejects it outright, so there is nothing
-- to replay — and that is the one place the slides' repair is spent.

open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational
open import Data.Unit.Base
open import Data.Vec.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Examples.ChimericLedger.Observable 1 (λ _ → [])
open import CategoricalCrypto.Examples.ChimericLedger.System 1 (λ _ → [])
open import CategoricalCrypto.OracleCall
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Examples.ChimericLedger.Replay where

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

rejected : proj₂ (runCall (λ _ → h) (applyTx inputConsuming s₀ txᵃ)) ≡ false
rejected = refl

------------------------------------------------------------------------
-- …as the headline property sees it
------------------------------------------------------------------------

-- Submit the same no-input transaction twice, then audit.
replay : Strat Query Answer
replay = ask (submit txᵃ) λ _ → ask (submit txᵃ) λ _ → ask audit λ _ → out false

replay-asks : asks≤ 3 replay
replay-asks _ _ _ = tt

chimeric-loses-value : Pr (Sys chimeric s₀) (auditWatch s₀ replay) ≡ 1ℚ
chimeric-loses-value = refl

consuming-preserves-value : Pr (Sys inputConsuming s₀) (auditWatch s₀ replay) ≡ 0ℚ
consuming-preserves-value = refl

------------------------------------------------------------------------
-- The birthday genesis is live
------------------------------------------------------------------------

-- `Pr` is 0ℚ both when the ledger is safe and when it is dead-locked, which
-- is what made an account-only genesis pass as a birthday target (external
-- theory review, finding 1).  So the genesis the birthday bound is proved at
-- is pinned live here.

h₀ h₁ : Hash
h₀ = replicate 1 false
h₁ = replicate 1 true

genesisUtxo : LState
genesisUtxo = genesis h₀ 0 2

spend : Strat Query Answer
spend = ask (submit (spendGenesis h₀ 0 2)) λ a → out (accepted a)

-- Accepted with probability 1, through the oracle.  At an account-only
-- genesis this is 0ℚ: `checkIns` rejects every input against an empty UTxO
-- set and `consumes inputConsuming` demands one.
genesis-live : Pr (Sys inputConsuming genesisUtxo) spend ≡ 1ℚ
genesis-live = refl

-- …and the state moves: the genesis output is consumed and its value
-- reappears under the transaction's own hash.
genesis-moves : proj₁ (runCall (λ _ → h₁) (applyTx inputConsuming genesisUtxo
                                             (spendGenesis h₀ 0 2)))
              ≡ (((h₁ , 0) , (0 , 2)) ∷ [] , [])
genesis-moves = refl

genesis-preserves : PrHit (Sys inputConsuming genesisUtxo) (badTotal genesisUtxo) spend ≡ 0ℚ
genesis-preserves = refl
