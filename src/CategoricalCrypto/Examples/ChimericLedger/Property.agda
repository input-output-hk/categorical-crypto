{-# OPTIONS --safe --without-K --guardedness #-}

-- Preservation of value, as ONE predicate about a family of ledger systems:
--
--     PreservesValue a V R   —   no polynomially query-bounded environment
--     ever gets the ledger to answer an audit with a total different from the
--     one it started with, except with negligible probability.
--
-- Library vocabulary it is built from, once each:
--   `Systems B`  a closed system for every security parameter `n`
--   `Watch B`    a transformation of environments, reporting a designated event
--   `Strat`      an environment: ask a query, read the answer, flip a coin, out
--   `asks≤ q d`  `d` asks at most `q` queries
--   `Pr P d`     the probability that `d` outputs `true` against `P`

open import Data.Bool.Base using (Bool; false)
open import Data.List.Base using (List)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly
open import Data.Nat.Properties using (≤-refl)
open import Data.Rational as ℚ using (ℚ)
open import Data.Vec.Base using (replicate)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Approximate.Decay
open import CategoricalCrypto.UC.Asymptotic
open import CategoricalCrypto.UC.Saturated

import CategoricalCrypto.Examples.ChimericLedger.Birthday   as Birthday
import CategoricalCrypto.Examples.ChimericLedger.Observable as Observable
import CategoricalCrypto.Examples.ChimericLedger.System     as System

module CategoricalCrypto.Examples.ChimericLedger.Property
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

-- The two per-level modules, read at the schedule; `Transfer` reuses both.
module AtLevel (n : ℕ) = System     n (ser n)
module Watched (n : ℕ) = Observable n (ser n)

-- Injectivity of the whole `ser` family: what the birthday theorem asks at
-- each level, and all this example assumes about serialization.  It is per
-- level because `Tx` depends on the hash width, so a single `ser` cannot be
-- typed.
SerInj : Set
SerInj = (n : ℕ) {t u : Ledger.Tx n} → ser n t ≡ ser n u → t ≡ u

------------------------------------------------------------------------
-- The schedule
------------------------------------------------------------------------

-- Hash width `n` at security parameter `n`: then the birthday bound reads
-- `(q² + q)·2⁻ⁿ`, negligible at every polynomial allowance.  Any schedule
-- with `n ≤ ℓ n` would do — that inequality is all the arithmetic spends.
LedgerIf^ω : ℕ → Iface
LedgerIf^ω = AtLevel.LedgerIf

εᴸ : ℕ → ℕ → ℚ
εᴸ n q = fromℕ (q ℕ.* q ℕ.+ q) ℚ.* inv-pow-2 n

εᴸ-negligible : NegligibleBound εᴸ
εᴸ-negligible = negligibleBound-inv-pow-2 {t = λ _ q → q ℕ.* q ℕ.+ q} {sch = λ n → n}
                  (λ _ Pq → poly-+ (poly-* Pq Pq) Pq) (λ _ → ≤-refl)

h₀ : (n : ℕ) → Ledger.Hash n
h₀ n = replicate n false

------------------------------------------------------------------------
-- The ideal family, and the property
------------------------------------------------------------------------

module _ (a V : ℕ) where

  genesisAt : (n : ℕ) → Ledger.LState n
  genesisAt n = AtLevel.genesis n (h₀ n) a V

  Ideal : Systems LedgerIf^ω
  Ideal n = AtLevel.Sys n inputConsuming (genesisAt n)

  auditWatch : Watch LedgerIf^ω
  auditWatch n = Watched.auditWatch n (genesisAt n)

  auditWatch-preserving : QueryPreserving auditWatch
  auditWatch-preserving n q d = Watched.asks≤-auditWatch n (genesisAt n) q false d

  PreservesValue : Systems LedgerIf^ω → Set
  PreservesValue R = SaturatedBoundedᴺ R auditWatch εᴸ

  -- The proved birthday theorem, read at the schedule and through the watch:
  -- the ideal side of the end-to-end statement, with no UC in it.
  ideal-preserves-value : SerInj → PreservesValue Ideal
  ideal-preserves-value si = boundedᴺ {I = Ideal} {ε = εᴸ} {bad = auditWatch} λ n →
    Watched.auditWatch-bounded n inputConsuming (genesisAt n)
      (Birthday.target n (ser n) (h₀ n) (si n) a V)
