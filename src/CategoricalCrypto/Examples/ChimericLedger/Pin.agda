{-# OPTIONS --safe --without-K #-}

-- Computed pins: the whole system — oracle sampling, protocol composition,
-- state trajectory, ℚ arithmetic — runs by `refl` at 1-bit hashes.

open import Data.Bool.Base using (false; true)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Rational using (0ℚ; 1ℚ)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Examples.ChimericLedger.POV 1 (λ _ → [])
open import CategoricalCrypto.OracleCall using (runCall)
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Examples.ChimericLedger.Pin where

open Ledger 1
open Step (λ _ → [])
open Replay using (s₀; txᵃ)

-- Submit the same no-input transaction twice, adaptively but blindly.
replay : Strat Query Answer
replay = ask (submit txᵃ) λ _ → ask (submit txᵃ) λ _ → out false

replay-asks : asks≤ 2 replay
replay-asks _ _ = tt

-- The chimeric ledger loses a unit of value with probability 1 …
chimeric-violates : PrHit (Sys chimeric s₀) (badTotal s₀) replay ≡ 1ℚ
chimeric-violates = refl

-- … and the input-consuming repair never leaves the initial total.
consuming-safe : PrHit (Sys inputConsuming s₀) (badTotal s₀) replay ≡ 0ℚ
consuming-safe = refl

------------------------------------------------------------------------
-- The birthday genesis is live
------------------------------------------------------------------------

-- Nothing above sees a vacuous experiment: `PrHit` is 0ℚ both when the ledger
-- is safe and when it is dead-locked, which is what made the account-only
-- genesis pass as a birthday target (external theory review, finding 1).  So
-- the genesis of `POV.AtBirthday` is pinned live here.

h₀ h₁ : Hash
h₀ = replicate 1 false
h₁ = replicate 1 true

gen : LState
gen = genesis h₀ 0 2

spend : Strat Query Answer
spend = ask (submit (spendGenesis h₀ 0 2)) λ a → out (accepted a)

-- Accepted with probability 1, through the oracle.  At the account-only
-- genesis this is 0ℚ: `checkIns` rejects every input against an empty UTxO set
-- and `consumes inputConsuming` demands one, so no transaction is acceptable.
genesis-live : Pr (Sys inputConsuming gen) spend ≡ 1ℚ
genesis-live = refl

-- …and the state moves: the genesis output is consumed and its value
-- reappears under the transaction's own hash.
genesis-moves : proj₁ (runCall (λ _ → h₁) (applyTx inputConsuming gen (spendGenesis h₀ 0 2)))
              ≡ (((h₁ , 0) , (0 , 2)) ∷ [] , [])
genesis-moves = refl

genesis-preserves : PrHit (Sys inputConsuming gen) (badTotal gen) spend ≡ 0ℚ
genesis-preserves = refl
