{-# OPTIONS --safe --without-K --guardedness #-}

-- The ideal ledger's monitored bound, with no UC vocabulary in it.
--
-- `pov-target` is the acceptance test of the audit interface: the PROVED
-- birthday theorem — a statement about state trajectories — read through
-- `monitor`, the strategy transformation whose verdict
-- `ChimericLedger.Trajectory` proves is exactly the trajectory violation (sound
-- by `monitor-sound`, complete on audited strategies by `monitor-complete`).
-- No hypothesis is added along the way.
--
-- This is the form the carries consume, levelwise.
-- `ChimericLedger.Schedule.ideal-bounded` is the family-level counterpart, at
-- the schedule's own `h₀`.

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import CategoricalCrypto.Examples.ChimericLedger

module CategoricalCrypto.Examples.ChimericLedger.Audit
  (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) where

open Ledger ℓ

open import CategoricalCrypto.Examples.ChimericLedger.Birthday ℓ ser
open import CategoricalCrypto.Examples.ChimericLedger.POV ℓ ser
open import CategoricalCrypto.Examples.ChimericLedger.Trajectory ℓ ser

pov-target : (h₀ : Hash) (ser-inj : {t u : Tx} → ser t ≡ ser u → t ≡ u)
             (a : Addr) (V : ℕ)
           → let s₀ = genesis h₀ a V in
             POVmonitor inputConsuming s₀ (AtBirthday.εbirthday h₀ ser-inj)
pov-target h₀ ser-inj a V =
  monitor-bounded inputConsuming s₀ (target h₀ ser-inj a V)
  where s₀ = genesis h₀ a V
