{-# OPTIONS --safe --without-K --guardedness #-}

-- The two safety properties of a family of ledger systems: `PreservesValue`
-- (interface-observable: the audit monitor's flag, read at every certified
-- context, `UC.Machine.Monitor`) and `StateSafe` (a supplied state test,
-- sampled at the protocol's idle states).  How they relate and what each
-- does not say: `…ChimericLedger.Transfer`.  Walkthrough: `docs/end-to-end.md` §4.

open import Data.Bool.Base
open import Data.List.Base using (List)
open import Data.Nat.Base as ℕ
open import Data.Nat.Poly
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties.Ext
open import Data.Vec.Base
open import Relation.Binary.PropositionalEquality

import Data.Rational.Properties as ℚP

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Agree
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Approximate.Decay
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.EventBounds
open import CategoricalCrypto.UC.Machine.Monitor
open import CategoricalCrypto.UC.Machine.StateEvent.Adequacy
open import CategoricalCrypto.UC.Machine.StateEvent.Read
open import CategoricalCrypto.UC.Model.Family.Emulation
open import CategoricalCrypto.UC.Quantitative.EventLift

import CategoricalCrypto.Examples.ChimericLedger.Birthday   as Birthday
import CategoricalCrypto.Examples.ChimericLedger.Observable as Observable
import CategoricalCrypto.Examples.ChimericLedger.System     as System

module CategoricalCrypto.Examples.ChimericLedger.Property
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

module AtLevel (n : ℕ) = System     n (ser n)
module Watched (n : ℕ) = Observable n (ser n)

SerInj : Set
SerInj = (n : ℕ) {t u : Ledger.Tx n} → ser n t ≡ ser n u → t ≡ u

------------------------------------------------------------------------
-- The schedule
------------------------------------------------------------------------

-- Hash width `n` at security parameter `n`, so the birthday bound reads
-- `(q² + q)·2⁻ⁿ`; any width `ℓ n ≥ n` would do (the `≤-refl` in `εᴸ-negligible`).
LedgerIf^ω : ℕ → Iface
LedgerIf^ω = AtLevel.LedgerIf

εᴸ : ℕ → ℕ → ℚ
εᴸ n q = fromℕ (q ℕ.* q ℕ.+ q) ℚ.* inv-pow-2 n

εᴸ-negligible : NegligibleBound εᴸ
εᴸ-negligible = negligibleBound-inv-pow-2 {t = λ _ q → q ℕ.* q ℕ.+ q}
                  (λ _ Pq → poly-+ (poly-* Pq Pq) Pq) (λ _ → ≤-refl)

0≤εᴸ : (n q : ℕ) → 0ℚ ℚ.≤ εᴸ n q
0≤εᴸ n q = 0≤* (0≤fromℕ (q ℕ.* q ℕ.+ q)) (0≤inv-pow-2 n)

h₀ : (n : ℕ) → Ledger.Hash n
h₀ n = replicate n false

------------------------------------------------------------------------
-- The two properties
------------------------------------------------------------------------

-- The source test `bad`, read on the machine at the protocol's `idle` states
-- only (`idleTest`): the boundaries `Protocol.Observe.PrHit` samples.
StateSafe : (R : Systems LedgerIf^ω) → ((n : ℕ) → St (R n) → Bool) → (ℕ → ℕ → ℚ) → Set₁
StateSafe R bad = StateBoundedᴺ (λ n → morphism (R n)) (λ n → idleTest (R n) (bad n))

module _ (t : ℕ) where

  auditWatch : (n : ℕ) → Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))
             → Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))
  auditWatch n = Watched.auditWatch n t

  -- The process spelling of that watch, which is what a context can be made
  -- to read: `UC.Quantitative.EventLift.agree` is the agreement between them.
  auditMonitorᶠ : (n : ℕ) → Proc (LedgerIf^ω n) (LedgerIf^ω n ⊗ᴵ Ωᴵ)
  auditMonitorᶠ n = monitorᴹ (Watched.reportsLoss n t)

  PreservesValue : Systems LedgerIf^ω → Set₁
  PreservesValue R = Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ εᴸ

  hitsᴸ : (R : Systems LedgerIf^ω) (n q : ℕ) {r : ℚ}
        → ((d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))) → asks≤ q d
           → Upper (runᴹ (morphism (R n)) (auditWatch n d)) r)
        → HitsAt q r (morphism (R n)) (auditMonitorᶠ n)
  hitsᴸ R n = hitsᵘ (Watched.reportsLoss n t) (morphism (R n))

  -- Read back at the context a strategy embeds to, where the compiled
  -- experiment is the watched run; nothing is spent returning.
  preservesValue⇒saturated :
      (R : Systems LedgerIf^ω) {ε : ℕ → ℕ → ℚ} → Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ ε
    → Saturated (λ n q r → (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))) → asks≤ q d
                         → Pr (R n) (auditWatch n d) ℚ.≤ r) ε
  preservesValue⇒saturated R {ε} = saturated-map {ε = ε} λ n q {r} → hits⇒bounded (Watched.reportsLoss n t) (R n) q {r}

  -- One-sided: the audited run flags at least the completed-hit mass of
  -- `bad` (detection/completeness).  Not two-sided adequacy of the audit,
  -- and silent on whether the audits interfere with the run.
  TruthfulAudit : (R : Systems LedgerIf^ω) → ((n : ℕ) → St (R n) → Bool) → Set
  TruthfulAudit R bad = (n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
                      → PrHit (R n) (bad n) d ℚ.≤ Pr (R n) (auditWatch n (Watched.withAudits n d))

  -- `withAudits` doubles the allowance (hence `q + q`); the lift to every admitted
  -- experiment is `UC.Machine.StateEvent.Adequacy`'s, exact.
  preservesValue⇒stateSafe : (R : Systems LedgerIf^ω) (bad : (n : ℕ) → St (R n) → Bool) {ε : ℕ → ℕ → ℚ}
                           → Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ ε → TruthfulAudit R bad
                           → StateSafe R bad (λ n q → ε n (q ℕ.+ q))
  preservesValue⇒stateSafe R bad {ε} pv truthful =
    hitᴺ⇒stateᴺ R bad (λ n → idleTest (R n) (bad n)) (λ _ _ → refl) (λ n q → ε n (q ℕ.+ q)) λ p Pp →
      let ν , neg , bnd = preservesValue⇒saturated R {ε} pv (λ n → p n ℕ.+ p n) (poly-+ Pp Pp)
      in ν , neg , λ n d ad → ℚP.≤-trans (truthful n d)
           (bnd n (Watched.withAudits n d) (Watched.asks≤-withAudits n (p n) d ad))

------------------------------------------------------------------------
-- The ideal family
------------------------------------------------------------------------

module _ (a V : ℕ) where

  genesisAt : (n : ℕ) → Ledger.LState n
  genesisAt n = AtLevel.genesis n (h₀ n) a V

  Ideal : Systems LedgerIf^ω
  Ideal n = AtLevel.Sys n inputConsuming (genesisAt n)

  ideal-bounded : SerInj → (n : ℕ) → Bounded (Ideal n) (auditWatch (genesisTotal V) n) (εᴸ n)
  ideal-bounded si n = Watched.auditWatch-bounded n inputConsuming (genesisAt n)
                         (Birthday.target n (ser n) (h₀ n) (si n) a V)

  ideal-preserves-value : SerInj → PreservesValue (genesisTotal V) Ideal
  ideal-preserves-value si =
    boundedᶠ⇒boundedᴺ _ _ εᴸ λ n q →
      hitsᴸ (genesisTotal V) Ideal n q λ d a → upper-run (Ideal n) (auditWatch (genesisTotal V) n d) (ideal-bounded si n q d a)

  badᴸ : (n : ℕ) → St (Ideal n) → Bool
  badᴸ n = Watched.badTotal n (genesisAt n)

  ideal-truthful : TruthfulAudit (genesisTotal V) Ideal badᴸ
  ideal-truthful n = Watched.auditWatch-complete n (AtLevel.oracle n) inputConsuming (genesisAt n)

  -- Straight from the birthday bound, at `εᴸ`: no audit is spent.
  ideal-conserves-value : SerInj → StateSafe Ideal badᴸ εᴸ
  ideal-conserves-value si =
    boundedᶠ⇒boundedᴺ _ _ εᴸ (boundedHit⇒stateᶠ Ideal badᴸ _ (λ _ _ → refl) εᴸ λ n →
      Birthday.target n (ser n) (h₀ n) (si n) a V)
