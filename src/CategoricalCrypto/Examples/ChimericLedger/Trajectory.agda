{-# OPTIONS --safe --without-K #-}

-- The audit answer is truthful: the trajectory statement and what a monitor
-- reading that answer reports are the same statement, on the audit-interleaved
-- strategy.
--
-- `audited d` asks `audit` after EVERY answer, so every state the trajectory
-- observable inspects is audited at the boundary it is inspected.  Two facts
-- make each comparison an induction with nothing else in it: an audit answer is
-- definitionally the truth about the state it is asked at
-- (`step (Sys …) (s , tbl) audit = ret ((s , tbl) , totalIs (total s))`), and
-- the test on that answer is literally `badTotal`'s.  So no persistence
-- argument is needed — `hitFrom`'s accumulator and the monitor's fire at
-- exactly the same boundaries.
--
-- `trajectoryFromAudit` is the `watch` form, which STOPS at the first
-- violation; the extra chances it takes on the strategy's own audit queries
-- only help that inequality.  It has no converse: an early `out true` weighs 1
-- where the continued trajectory run may deadlock and weigh nothing.  So the
-- observable the UC layer designates is `monitor`, which accumulates instead
-- and therefore has BOTH directions — `monitor-sound` is what lets an ideal
-- trajectory bound supply the graded premise
-- (`docs/protocol-implementation-review.md` §1), `monitor-complete` is what
-- keeps the premise from being a statement about a blind monitor.

open import Data.Bool.Base using (Bool; true; false; not; _∨_; if_then_else_; f≤t; b≤b)
  renaming (_≤_ to _≤ᵇ_)
open import Data.Bool.Properties using (T-≡; ≤-minimum)
open import Data.Bool.Properties.Ext using (∨-mono; ∨-monoʳ)
open import Data.List.Base using (List)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ) renaming (_≡ᵇ_ to _≡ᴺ_)
open import Data.Nat.Properties using (≡⇒≡ᵇ)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Data.Rational using (ℚ; 1ℚ) renaming (_≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Data.Rational.Properties.Ext using (0≤1ℚ)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Prelude
open import ProbabilisticLogic.Distribution.RationalDist using (lookupᴰℚ-return)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using
  (E-bind; E-mono; E⊥-bind; E⊥-mono; Pr₁⊥≤1)
open import ProbabilisticLogic.Distribution.Uniform using (bool→ℚ)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Examples.ChimericLedger.Trajectory
  (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) where

open Ledger ℓ

open import CategoricalCrypto.Examples.ChimericLedger.POV ℓ ser

-- Nothing below reads the hash implementation: an audit query is answered from
-- the ledger's own state (`served`) and the trajectory event ignores the second
-- component, so the argument is the same at the random oracle and at any real
-- hash.  `ChimericLedger.Real` spends the general case on the real side.
module _ (hash : Protocol unitᴵ HashIf) (vr : Variant) (s₀ : LState) where

  private
    P = Sysᴴ hash vr s₀

    Bad : St P → Bool
    Bad = badTotal s₀

    -- What a leaf reports: the verdict it carries, whichever of the two
    -- readings reached it.
    verdict : (b : Bool) → Pr₁⊥ (return⊥ b) ≡ bool→ℚ b
    verdict b = lookupᴰℚ-return (just b) mb

    -- An audit query does not move the state and its answer is that state's
    -- own total, so a run through one is the run that follows it.
    served : (st : St P) (G : St P × Answer → Dist⊥ Bool)
           → Pr₁⊥ (kernel P st audit >>=⊥ G)
             ≡ Pr₁⊥ (G (st , totalIs (total (proj₁ st))))
    served st G = Pr₁⊥-cong (kernel P st audit >>=⊥ G)
                            (G (st , totalIs (total (proj₁ st))))
                            (>>=⊥-identityˡ (st , totalIs (total (proj₁ st))) G)

  mutual

    -- The comparison at an arbitrary reachable state, the accumulator still
    -- clear.  `≤` and not `≡` only because of the strategy's own audit
    -- queries: `watch` may stop on one of those before the trajectory does.
    core : (st : St P) (d : Strat Query Answer)
         → Pr₁⊥ (hitFrom P Bad false st d)
           ≤ℚ Pr₁⊥ (runFrom P st (watch s₀ (audited d)))
    core st (out b)    = ≤-refl
    core st (coin μ k) =
      ≤-trans (≤-reflexive (E-bind μ Hb mb))
      (≤-trans (E-mono μ (λ b → Pr₁⊥ (Hb b)) (λ b → Pr₁⊥ (Rb b)) (λ b → core st (k b)))
               (≤-reflexive (sym (E-bind μ Rb mb))))
      where
      Hb Rb : Bool → Dist⊥ Bool
      Hb b = hitFrom P Bad false st (k b)
      Rb b = runFrom P st (watch s₀ (audited (k b)))
    core st (ask q k) =
      ≤-trans (≤-reflexive (E⊥-bind μq H bool→ℚ))
      (≤-trans (E⊥-mono μq (λ x → Pr₁⊥ (H x)) (λ x → Pr₁⊥ (R x)) ptw)
               (≤-reflexive (sym (E⊥-bind μq R bool→ℚ))))
      where
      μq = kernel P st q

      H R : St P × Answer → Dist⊥ Bool
      H (st′ , r) = hitFrom P Bad (Bad st′) st′ (k r)
      R (st′ , r) = runFrom P st′
        (if violates s₀ r then out true else watch s₀ (ask audit λ _ → audited (k r)))

      ptw : (x : St P × Answer) → Pr₁⊥ (H x) ≤ℚ Pr₁⊥ (R x)
      ptw (st′ , r) with violates s₀ r
      ... | true  = ≤-trans (Pr₁⊥≤1 (hitFrom P Bad (Bad st′) st′ (k r)))
                            (≤-reflexive (sym (verdict true)))
      ... | false = auditStep st′ (k r)

    -- The audit query itself: it does not move the state, and its answer is
    -- the state's own `total`, so `watch`'s test on it IS `Bad`.
    auditStep : (st : St P) (c : Strat Query Answer)
              → Pr₁⊥ (hitFrom P Bad (Bad st) st c)
                ≤ℚ Pr₁⊥ (runFrom P st (watch s₀ (ask audit λ _ → audited c)))
    auditStep (s , tbl) c = ≤-trans body (≤-reflexive (sym (served (s , tbl) G)))
      where
      G : St P × Answer → Dist⊥ Bool
      G (st′ , r) = runFrom P st′
        (if violates s₀ r then out true else watch s₀ (audited c))

      body : Pr₁⊥ (hitFrom P Bad (Bad (s , tbl)) (s , tbl) c)
           ≤ℚ Pr₁⊥ (G ((s , tbl) , totalIs (total s)))
      body with total s ≡ᴺ total s₀
      ... | true  = core (s , tbl) c
      ... | false = ≤-trans (Pr₁⊥≤1 (hitFrom P Bad true (s , tbl) c))
                            (≤-reflexive (sym (verdict true)))

  -- The genesis state is not itself a violation, so the run starts clear.
  private
    init-good : Bad (s₀ , init hash) ≡ false
    init-good = cong not (Equivalence.to T-≡ (≡⇒≡ᵇ (total s₀) (total s₀) refl))

  -- `POV.TrajectoryFromAudit vr s₀`, at the hash implementation `hash`.
  trajectoryFromAudit : (d : Strat Query Answer)
                      → PrHit P Bad d ≤ℚ Pr P (watch s₀ (audited d))
  trajectoryFromAudit d =
    subst (λ b → Pr₁⊥ (hitFrom P Bad b (s₀ , init hash) d)
                 ≤ℚ Pr₁⊥ (runFrom P (s₀ , init hash) (watch s₀ (audited d))))
          (sym init-good) (core (s₀ , init hash) d)

  ------------------------------------------------------------------------
  -- The designated monitor

  -- `monitor`'s accumulator against the trajectory's, at any two accumulators
  -- the first of which is behind: the Boolean order carries "behind" through
  -- the induction, which is what an accumulating monitor needs in place of a
  -- separate monotonicity lemma for either reading.
  --
  -- SOUND: the monitor reports nothing the trajectory did not have.  A
  -- `submit` acknowledgement it does not read at all, and an audit answer is
  -- the audited state's own total, so its accumulator is `hitFrom`'s at that
  -- boundary.  This is the direction `watch` does not have — its early
  -- `out true` weighs 1 where the continued trajectory run may deadlock.
  sound : {acc acc′ : Bool} → acc ≤ᵇ acc′ → (st : St P) (d : Strat Query Answer)
        → Pr₁⊥ (runFrom P st (monitorFrom s₀ acc d))
          ≤ℚ Pr₁⊥ (hitFrom P Bad acc′ st d)
  sound b≤b _  (out _) = ≤-refl
  sound f≤t _  (out _) =
    ≤-trans (≤-reflexive (verdict false)) (≤-trans 0≤1ℚ (≤-reflexive (sym (verdict true))))
  sound {acc} {acc′} le st (coin μ k) =
    ≤-trans (≤-reflexive (E-bind μ Lb mb))
    (≤-trans (E-mono μ (λ b → Pr₁⊥ (Lb b)) (λ b → Pr₁⊥ (Rb b)) (λ b → sound le st (k b)))
             (≤-reflexive (sym (E-bind μ Rb mb))))
    where
    Lb Rb : Bool → Dist⊥ Bool
    Lb b = runFrom P st (monitorFrom s₀ acc (k b))
    Rb b = hitFrom P Bad acc′ st (k b)
  sound {acc} {acc′} le st (ask (submit tx) k) =
    ≤-trans (≤-reflexive (E⊥-bind μq L bool→ℚ))
    (≤-trans (E⊥-mono μq (λ x → Pr₁⊥ (L x)) (λ x → Pr₁⊥ (R x)) ptw)
             (≤-reflexive (sym (E⊥-bind μq R bool→ℚ))))
    where
    μq = kernel P st (submit tx)

    L R : St P × Answer → Dist⊥ Bool
    L (st′ , r) = runFrom P st′ (monitorFrom s₀ (acc ∨ false) (k r))
    R (st′ , r) = hitFrom P Bad (acc′ ∨ Bad st′) st′ (k r)

    ptw : (x : St P × Answer) → Pr₁⊥ (L x) ≤ℚ Pr₁⊥ (R x)
    ptw (st′ , r) = sound (∨-mono le (≤-minimum (Bad st′))) st′ (k r)
  sound {acc} {acc′} le (s , tbl) (ask audit k) =
    ≤-trans (≤-reflexive (served (s , tbl) L))
    (≤-trans (sound (∨-mono le b≤b) (s , tbl) (k (totalIs (total s))))
             (≤-reflexive (sym (served (s , tbl) R))))
    where
    L R : St P × Answer → Dist⊥ Bool
    L (st′ , r) = runFrom P st′ (monitorFrom s₀ (acc ∨ violates s₀ r) (k r))
    R (st′ , r) = hitFrom P Bad (acc′ ∨ Bad st′) st′ (k r)

  -- COMPLETE: on the audit-interleaved strategy the monitor misses nothing.
  -- Every state the trajectory inspects is audited at the boundary it is
  -- inspected, and the audit answer there is `Bad`, so no case on the query is
  -- needed — what the monitor reads of `d`'s own answers can only help.
  complete : {acc acc′ : Bool} → acc ≤ᵇ acc′ → (st : St P) (d : Strat Query Answer)
           → Pr₁⊥ (hitFrom P Bad acc st d)
             ≤ℚ Pr₁⊥ (runFrom P st (monitorFrom s₀ acc′ (audited d)))
  complete b≤b _  (out _) = ≤-refl
  complete f≤t _  (out _) =
    ≤-trans (≤-reflexive (verdict false)) (≤-trans 0≤1ℚ (≤-reflexive (sym (verdict true))))
  complete {acc} {acc′} le st (coin μ k) =
    ≤-trans (≤-reflexive (E-bind μ Hb mb))
    (≤-trans (E-mono μ (λ b → Pr₁⊥ (Hb b)) (λ b → Pr₁⊥ (Rb b)) (λ b → complete le st (k b)))
             (≤-reflexive (sym (E-bind μ Rb mb))))
    where
    Hb Rb : Bool → Dist⊥ Bool
    Hb b = hitFrom P Bad acc st (k b)
    Rb b = runFrom P st (monitorFrom s₀ acc′ (audited (k b)))
  complete {acc} {acc′} le st (ask q k) =
    ≤-trans (≤-reflexive (E⊥-bind μq H bool→ℚ))
    (≤-trans (E⊥-mono μq (λ x → Pr₁⊥ (H x)) (λ x → Pr₁⊥ (R x)) ptw)
             (≤-reflexive (sym (E⊥-bind μq R bool→ℚ))))
    where
    μq = kernel P st q

    H R : St P × Answer → Dist⊥ Bool
    H (st′ , r) = hitFrom P Bad (acc ∨ Bad st′) st′ (k r)
    R (st′ , r) = runFrom P st′
      (monitorFrom s₀ (acc′ ∨ violatesAt s₀ q r) (ask audit λ _ → audited (k r)))

    -- What the injected audit query leads to, whatever it finds.
    after : (r : Answer) → St P × Answer → Dist⊥ Bool
    after r (st″ , a) = runFrom P st″
      (monitorFrom s₀ ((acc′ ∨ violatesAt s₀ q r) ∨ violates s₀ a) (audited (k r)))

    ptw : (x : St P × Answer) → Pr₁⊥ (H x) ≤ℚ Pr₁⊥ (R x)
    ptw (st′ , r) =
      ≤-trans (complete (∨-mono (∨-monoʳ le) b≤b) st′ (k r))
              (≤-reflexive (sym (served st′ (after r))))

  monitor-sound : (d : Strat Query Answer)
                → Pr P (monitor s₀ d) ≤ℚ PrHit P Bad d
  monitor-sound d =
    subst (λ b → Pr₁⊥ (runFrom P (s₀ , init hash) (monitor s₀ d))
                 ≤ℚ Pr₁⊥ (hitFrom P Bad b (s₀ , init hash) d))
          (sym init-good) (sound b≤b (s₀ , init hash) d)

  monitor-complete : (d : Strat Query Answer)
                   → PrHit P Bad d ≤ℚ Pr P (monitor s₀ (audited d))
  monitor-complete d =
    subst (λ b → Pr₁⊥ (hitFrom P Bad b (s₀ , init hash) d)
                 ≤ℚ Pr₁⊥ (runFrom P (s₀ , init hash) (monitor s₀ (audited d))))
          (sym init-good) (complete b≤b (s₀ , init hash) d)

------------------------------------------------------------------------
-- …at the random oracle, where the ideal bound lives

module _ (vr : Variant) (s₀ : LState) where

  -- The trajectory bound BECOMES the designated monitor's bound, which is what
  -- `ChimericLedger.Audit` hands to the UC layer's audit event, and comes back
  -- through `pov-via-monitor` at the audit-interleaved strategy's budget.
  monitor-bounded : {ε : ℕ → ℚ} → POV vr s₀ ε → POVmonitor vr s₀ ε
  monitor-bounded pov q d a = ≤-trans (monitor-sound oracle vr s₀ d) (pov q d a)

  pov-via-monitor : {ε : ℕ → ℚ} → POVmonitor vr s₀ ε → (qa : ℕ) (d : Strat Query Answer)
                  → asks≤ qa (audited d) → PrHit (Sys vr s₀) (badTotal s₀) d ≤ℚ ε qa
  pov-via-monitor pm qa d aa =
    ≤-trans (monitor-complete oracle vr s₀ d) (pm qa (audited d) aa)
