{-# OPTIONS --safe --without-K --guardedness #-}

-- The ledger at a security-parameter schedule: the ideal side of the
-- end-to-end theorem.
--
-- The birthday bound is proved at a FIXED hash width, and an asymptotic
-- statement needs a family.  The schedule taken here is the canonical one,
-- width `ℓ n = n`: then `εbirthday` reads `(q² + q)·2⁻ⁿ`, which is negligible
-- at every polynomial allowance (`UC.Approximate.Decay`), and any schedule
-- with `n ≤ ℓ n` would do — that inequality is all the arithmetic spends.
--
-- Serialization is PER LEVEL, `ser n` with its own injectivity, because `Tx`
-- itself depends on the width and a single `ser` cannot be typed.  The
-- injectivity hypothesis is passed on, never discharged: it is the birthday
-- theorem's own assumption.

open import Data.Bool.Base using (Bool; false)
open import Data.List.Base using (List)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly
open import Data.Nat.Properties using (≤-refl)
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ using (ℚ)
open import Data.Vec.Base using (replicate)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Asymptotic
open import CategoricalCrypto.UC.Approximate.Decay
open import CategoricalCrypto.UC.Saturated

import CategoricalCrypto.Examples.ChimericLedger.Birthday as Bday
import CategoricalCrypto.Examples.ChimericLedger.POV as POV
import CategoricalCrypto.Examples.ChimericLedger.Trajectory as Traj

module CategoricalCrypto.Examples.ChimericLedger.Schedule
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

module L  (n : ℕ) = POV  n (ser n)
module T  (n : ℕ) = Traj n (ser n)
module Bd (n : ℕ) = Bday n (ser n)

-- Injectivity of the whole family, which is what the birthday theorem asks at
-- each level and all this module assumes about `ser`.
SerInj : Set
SerInj = (n : ℕ) {t u : Ledger.Tx n} → ser n t ≡ ser n u → t ≡ u

------------------------------------------------------------------------
-- The schedule

LedgerIf^ω : ℕ → Iface
LedgerIf^ω = L.LedgerIf

-- `2⁻ⁿ` at a birthday numerator, and its negligibility: the whole of
-- acceptance requirement 1's arithmetic.
εᴸ : ℕ → ℕ → ℚ
εᴸ n q = fromℕ (q ℕ.* q ℕ.+ q) ℚ.* inv-pow-2 n

εᴸ-negligible : NegligibleBound εᴸ
εᴸ-negligible = negligibleBound-inv-pow-2 {t = λ _ q → q ℕ.* q ℕ.+ q} {sch = λ n → n}
                  (λ _ Pq → poly-+ (poly-* Pq Pq) Pq) (λ _ → ≤-refl)

h₀ : (n : ℕ) → Ledger.Hash n
h₀ n = replicate n false

------------------------------------------------------------------------
-- The ideal family

module _ (a V : ℕ) where

  gen : (n : ℕ) → Ledger.LState n
  gen n = L.genesis n (h₀ n) a V

  Ideal : Systems LedgerIf^ω
  Ideal n = L.Sys n inputConsuming (gen n)

  -- The designated observable: the monitor of `ChimericLedger.POV`, whose
  -- truthfulness about the trajectory is `ChimericLedger.Trajectory`'s theorem.
  monitorᴸ : Watch LedgerIf^ω
  monitorᴸ n = L.monitor n (gen n)

  auditedᴸ : (n : ℕ) → Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))
           → Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))
  auditedᴸ = L.audited

  badᴸ : Bad Ideal
  badᴸ n = L.badTotal n (gen n)

  monitorᴸ-preserving : QueryPreserving monitorᴸ
  monitorᴸ-preserving n q d = L.asks≤-monitor n (gen n) q false d

  auditedᴸ-asks : (n q : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
                → asks≤ q d → asks≤ (q ℕ.+ q) (auditedᴸ n d)
  auditedᴸ-asks = L.asks≤-audited

  -- The proved birthday theorem, read at the schedule and at the designated
  -- monitor: the ideal side of the end-to-end statement, with no UC in it.
  ideal-bounded : SerInj → (n : ℕ) → Bounded (Ideal n) (monitorᴸ n) (εᴸ n)
  ideal-bounded si n = T.monitor-bounded n inputConsuming (gen n)
                         (Bd.target n (h₀ n) (si n) a V)

  -- Preservation of value: no polynomially query-bounded environment ever
  -- gets the ledger to answer an audit with a total different from the one it
  -- started with, except with negligible probability.
  PreservesValue : Systems LedgerIf^ω → Set
  PreservesValue R = SaturatedBoundedᴺ R monitorᴸ εᴸ

  ideal-preserves-value : SerInj → PreservesValue Ideal
  ideal-preserves-value si = boundedᴺ {I = Ideal} {ε = εᴸ} {bad = monitorᴸ} (ideal-bounded si)

  -- …and the real side's obligation, named: UC identifies no internal state
  -- trajectory, so recovering one needs the implementation's own audit
  -- truthfulness.  `Trajectory.monitor-complete` is this for a ledger image;
  -- for a real system that is not one it is part of the statement.
  TruthfulAudit : (R : Systems LedgerIf^ω) → Bad R → Set
  TruthfulAudit R bad = (n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
                      → PrHit (R n) (bad n) d ℚ.≤ Pr (R n) (monitorᴸ n (auditedᴸ n d))

  ideal-truthful : TruthfulAudit Ideal badᴸ
  ideal-truthful n = T.monitor-complete n (L.oracle n) inputConsuming (gen n)
