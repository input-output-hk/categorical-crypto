{-# OPTIONS --safe --without-K #-}

-- Computed pins: the whole system — oracle sampling, protocol composition,
-- state trajectory, ℚ arithmetic — runs by `refl` at 1-bit hashes.

open import Data.Bool.Base using (false)
open import Data.List.Base using (List; [])
open import Data.Nat.Base using (ℕ)
open import Data.Rational using (0ℚ; 1ℚ)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Examples.ChimericLedger.POV 1 (λ _ → [])
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Examples.ChimericLedger.Pin where

open Ledger 1
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
