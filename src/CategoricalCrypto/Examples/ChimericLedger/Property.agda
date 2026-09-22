{-# OPTIONS --safe --without-K --guardedness #-}

-- Preservation of value, as ONE predicate about a family of ledger systems:
--
--     PreservesValue a V R   —   no admitted query-bounded environment,
--     however it interacts with the closed system, ever sees an audit answer
--     whose total differs from the one the ledger started with, except with
--     negligible probability.
--
-- The event is read by a MONITOR compiled into the environment's own test
-- (`UC.Machine.Monitor`): the compiled experiment's verdict IS the accumulated
-- flag, so the property quantifies over every certified context of the machine
-- model rather than over a vocabulary of strategies.  What that costs is one
-- query — the monitor's accumulator needs potential of its own
-- (`UC.Quantitative.EventLift.Cov`) — and it is visible in the schedule `εᴹ`.
--
-- Library vocabulary it is built from, once each:
--   `Systems B`     a closed system for every security parameter `n`
--   `auditMonitor`  relay the ledger interface, raising a flag on an audit
--                   answer whose total is not the initial one
--   `Hitsᴺ f μ ε`   at every polynomial allowance `p` there is a negligible
--                   slack `ν` bounding the flag's mass by `ε n (p n) + ν n`,
--                   uniformly over every context that allowance admits
--
-- `preservesValue⇒saturated` reads the same bound back at the contexts an
-- ordinary strategy embeds to, which is what the counterexamples and the
-- trajectory appendix consume.

open import Data.Bool.Base using (Bool; false)
open import Data.List.Base using (List)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly
open import Data.Nat.Properties using (*-mono-≤; +-mono-≤; ≤-refl)
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; nonNegative)
open import Data.Rational.Properties using (*-monoʳ-≤-nonNeg)
open import Data.Rational.Properties.Ext using (0≤*)
open import Data.Vec.Base using (replicate)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp.Advantage using (Upper)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Approximate.Decay
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.Machine.Monitor using (Flagᴵ)
open import CategoricalCrypto.UC.Quantitative.EventLift
  using (hits⇒bounded; hitsᵘ; ledger-hitsᵘ)
open import CategoricalCrypto.UC.Quantitative.Hits
  using (HitsAt; Hitsᴺ; auditMonitor; auditWatch-IsWatch; hitsᶠ⇒hitsᴺ)
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

-- `UC.Model.EventBounds.Monotone` at every level, which is what reading the
-- schedule at a CAP rather than at a context's carried allowance costs.
εᴸ-mono : (n : ℕ) {q q′ : ℕ} → q ℕ.≤ q′ → εᴸ n q ℚ.≤ εᴸ n q′
εᴸ-mono n le = *-monoʳ-≤-nonNeg (inv-pow-2 n) ⦃ nonNegative (0≤inv-pow-2 n) ⦄
                 (fromℕ-mono-≤ (+-mono-≤ (*-mono-≤ le le) le))

-- What makes a watch that never reports satisfy the property: the allowance
-- is never negative.
0≤εᴸ : (n q : ℕ) → 0ℚ ℚ.≤ εᴸ n q
0≤εᴸ n q = 0≤* (0≤fromℕ (q ℕ.* q ℕ.+ q)) (0≤inv-pow-2 n)

-- …and the same schedule read one query further: the honest allowance the
-- COMPILED experiment leaves a strategy is the environment's own cap plus the
-- monitor's accumulator, and that unit is the whole of what monitoring costs
-- this example's number.
εᴹ : ℕ → ℕ → ℚ
εᴹ n q = εᴸ n (q ℕ.+ 1)

εᴹ-negligible : NegligibleBound εᴹ
εᴹ-negligible = GradedBound-reindex Negligible (λ _ q → q ℕ.+ 1)
                  (λ _ Pp → poly-+ Pp (poly-const 1)) εᴸ εᴸ-negligible

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

  -- The process spelling of that watch, which is what a context can be made
  -- to read: `UC.Machine.Monitor.Agree.agree` is the agreement between them.
  auditMonitorᶠ : (n : ℕ) → Proc (LedgerIf^ω n) (LedgerIf^ω n ⊗ᴵ Flagᴵ)
  auditMonitorᶠ n = auditMonitor n (ser n) (genesisAt n)

  PreservesValue : Systems LedgerIf^ω → Set₁
  PreservesValue R = Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ εᴹ

  -- The lift, at one level and one allowance: a bound on the watched strategy
  -- run bounds the monitored run of every certified context that allowance
  -- admits.  Every positive instance of the property below goes through it.
  hitsᴸ : (R : Systems LedgerIf^ω) (n q : ℕ) {r : ℚ}
        → ((d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))) → asks≤ (q ℕ.+ 1) d
           → Upper (runᴹ (morphism (R n)) (auditWatch n d)) r)
        → HitsAt q r (morphism (R n)) (auditMonitorᶠ n)
  hitsᴸ R n = hitsᵘ (Watched.reportsLoss n (genesisAt n))
                    (Watched.auditWatchFrom n (genesisAt n))
                    (auditWatch-IsWatch n (ser n) (genesisAt n)) (morphism (R n))

  -- …and back, at the context an ordinary strategy embeds to, where the
  -- compiled experiment IS the watched run.  Nothing is spent returning: the
  -- extra query was charged on the way out.
  preservesValue⇒saturated : (R : Systems LedgerIf^ω)
                           → PreservesValue R → SaturatedBoundedᴺ R auditWatch εᴹ
  preservesValue⇒saturated R pv p Pp =
    let ν , neg , bnd = pv p Pp
    in ν , neg , λ n → hits⇒bounded (Watched.reportsLoss n (genesisAt n))
                         (Watched.auditWatchFrom n (genesisAt n))
                         (auditWatch-IsWatch n (ser n) (genesisAt n)) (R n) (p n) (bnd n)

  -- The proved birthday theorem, read at the schedule and through the watch:
  -- the ideal side of the end-to-end statement, with no UC in it.
  ideal-bounded : SerInj → (n : ℕ) → Bounded (Ideal n) (auditWatch n) (εᴸ n)
  ideal-bounded si n = Watched.auditWatch-bounded n inputConsuming (genesisAt n)
                         (Birthday.target n (ser n) (h₀ n) (si n) a V)

  ideal-preserves-value : SerInj → PreservesValue Ideal
  ideal-preserves-value si = hitsᶠ⇒hitsᴺ _ auditMonitorᶠ εᴹ λ n →
    ledger-hitsᵘ n (ser n) (genesisAt n) inputConsuming (ideal-bounded si n)
