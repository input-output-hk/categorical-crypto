{-# OPTIONS --safe --without-K --guardedness #-}

-- Event bounds at the compiled monitor, and the strategy-to-contexts lift
-- (`docs/event-bounds-in-setup.md` §5).
--
-- A monitored event is a state event: `monitorᴹ report ∘ u` is the flag wire
-- of the accumulator `accᴹ report u` (`UC.Machine.Monitor.monitor-flag`), so
-- the lift is `UC.Machine.StateEvent.Lift.stateLift` there, and the premise
-- is read back at the watch by `flag-agree`.

open import Categories.Category

open import Data.Bool.Base
open import Data.Nat.Base as ℕ
open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ)
open import Data.Unit.Base

import Data.Nat.Properties as ℕP

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Agree
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge
open import CategoricalCrypto.UC.Machine.EventBounds
open import CategoricalCrypto.UC.Machine.Monitor
open import CategoricalCrypto.UC.Machine.Monitor.Agree
open import CategoricalCrypto.UC.Machine.StateEvent.Agree
open import CategoricalCrypto.UC.Machine.StateEvent.Lift
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.Seam

module CategoricalCrypto.UC.Quantitative.EventLift where

private module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- Event bounds at the monitored readout

-- A COMPLETED-RUN event, as `Protocol.Observe.PrHit` is: the flag is read only
-- when the closed experiment returns its verdict, so a run that raises it and
-- then diverges contributes nothing; prefix reachability is a different event
-- (`docs/state-event-contract.md` §1, row 11).
HitsAt : {A B : Iface} → ℕ → ℚ → Proc A B → Proc B (B ⊗ᴵ Ωᴵ) → Set₁
HitsAt {B = B} q r f μ = BoundedAt q r (μ 𝒫.∘ f) (flagReader B)

Hitsᴺ : {A B : ℕ → Iface} → ((n : ℕ) → Proc (A n) (B n))
      → ((n : ℕ) → Proc (B n) (B n ⊗ᴵ Ωᴵ)) → (ℕ → ℕ → ℚ) → Set₁
Hitsᴺ {B = B} f μ ε = Boundedᴺ (λ n → μ n 𝒫.∘ f n) (λ n → flagReader (B n)) ε

------------------------------------------------------------------------
-- The lift

-- A bound on the watched run of every affordable strategy is an event bound
-- at every context of that cap (`UC.Machine.EventBounds.BoundedAt`), exactly.
hitsᵘ : {B : Iface} (report : Neg B → Pos B → Bool) (u : Proc unitᴵ B) (q : ℕ) {r : ℚ}
      → ((d : Strat (Neg B) (Pos B)) → asks≤ q d → Upper (runᴹ u (watchFrom report false d)) r)
      → HitsAt q r u (monitorᴹ report)
hitsᵘ {B} report u q h Y E m qE qm le =
  upper-≈ (readRun-resp-≈ Y (monitor-flag report u) (flagReader B) E m)
    (stateLift (accᴹ report u) (reported report u) q
       (λ d a → upper-≈ (flag-agree report u d) (h d a))
       Y E m qE qm le)

------------------------------------------------------------------------
-- …and back to the strategy level

-- The monitored process is the accumulator's flag wire (`monitor-flag`), so
-- this is `stateRead-agree` followed by `flag-agree`.
agree : (B : Iface) (report : Neg B → Pos B → Bool) (u : Proc unitᴵ B) (d : Strat (Neg B) (Pos B))
      → readRun unitᴵ (monitorᴹ report 𝒫.∘ u) (flagReader B) (stratTest B d) m₀
        ≈ₚ runᴹ u (watchFrom report false d)
agree B report u d =
      readRun-resp-≈ unitᴵ (monitor-flag report u) (flagReader B) (stratTest B d) m₀
  ⟨≈⟩ stateRead-agree (accᴹ report u) (reported report u) d
  ⟨≈⟩ flag-agree report u d

-- A contextual event bound read at `stratTest` IS the strategy-level watched
-- bound at the same cap: the closure is closed, so `scale q (positive 0) = q`.
hits⇒upper : {B : Iface} (report : Neg B → Pos B → Bool) (u : Proc unitᴵ B) (q : ℕ) {r : ℚ}
           → HitsAt q r u (monitorᴹ report)
           → (d : Strat (Neg B) (Pos B)) → asks≤ q d → Upper (runᴹ u (watchFrom report false d)) r
hits⇒upper {B} report u q h d a =
  upper-≈ (≈sym (agree B report u d))
          (h unitᴵ (stratTest B d) m₀ (qb-stratTest B d a) (qb-closed m₀) (ℕP.≤-reflexive (scale-unit q)))

hits⇒bounded :
    {B : Iface} (report : Neg B → Pos B → Bool)
  → (P : Protocol unitᴵ B) (q : ℕ) {r : ℚ}
  → HitsAt q r (morphism P) (monitorᴹ report)
  → (d : Strat (Neg B) (Pos B)) → asks≤ q d → Pr P (watchFrom report false d) ℚ.≤ r
hits⇒bounded report P q h d a = run-upper P (watchFrom report false d) (hits⇒upper report (morphism P) q h d a)
