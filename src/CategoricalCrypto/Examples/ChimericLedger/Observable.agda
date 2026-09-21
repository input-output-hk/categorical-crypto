{-# OPTIONS --safe --without-K #-}

-- What an environment can see of a loss of value, and why it may be believed.
--
-- `auditWatch` plays a strategy unchanged and accumulates `true` the first
-- time an audit answer reports a total other than the initial one.  Stopping
-- at the first violation instead would cost `auditWatch-sound` — an early
-- `out true` weighs 1 where the continued run may deadlock and weigh nothing
-- (`docs/protocol-implementation-review.md` §1).
--
-- `badTotal` is the same event read off the STATE TRAJECTORY, which no
-- environment sees.  The two are tied here: `auditWatch-sound` says the watch
-- reports nothing the trajectory did not have, and `auditWatch-complete` says
-- that on the audit-interleaved strategy `withAudits d` it misses nothing.
-- Both are inductions with nothing else in them, because an audit answer is
-- definitionally the truth about the state it is asked at
-- (`step (Sys …) (s , tbl) audit = ret ((s , tbl) , totalIs (total s))`) and
-- the test on that answer is literally `badTotal`'s.

open import Data.Bool.Base using (Bool; true; false; not; _∨_; f≤t; b≤b)
  renaming (_≤_ to _≤ᵇ_)
open import Data.Bool.Properties using (T-≡; ≤-minimum)
open import Data.Bool.Properties.Ext
open import Data.List.Base using (List)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ᴺ_; _≡ᵇ_ to _≡ᴺ_)
open import Data.Nat.Properties using (+-suc; ≡⇒≡ᵇ)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Data.Rational using (ℚ) renaming (_≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Data.Rational.Properties.Ext
open import Data.Unit.Base using (tt)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Prelude
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Examples.ChimericLedger.Observable
  (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) where

open Ledger ℓ

open import CategoricalCrypto.Examples.ChimericLedger.System ℓ ser

------------------------------------------------------------------------
-- The two readings of "value was lost"
------------------------------------------------------------------------

-- The system's state is the two components'; the ledger's is the first, and
-- the hash implementation's — whatever it holds — is not read at all.
badTotal : {S : Set} → LState → LState × S → Bool
badTotal s₀ st = not (total (proj₁ st) ≡ᴺ total s₀)

module _ (s₀ : LState) where

  lostValue : Answer → Bool
  lostValue (ok _)      = false
  lostValue (totalIs t) = not (t ≡ᴺ total s₀)

  -- The TRUSTED reading of an answer: a `totalIs` answer is the audited
  -- state's own total, so it may be believed; nothing makes a `submit`
  -- acknowledgement a report about the state, so it is not read at all.
  reportsLoss : Query → Answer → Bool
  reportsLoss (submit _) _ = false
  reportsLoss audit      a = lostValue a

  auditWatchFrom : Bool → Strat Query Answer → Strat Query Answer
  auditWatchFrom acc (out _)    = out acc
  auditWatchFrom acc (ask q k)  = ask q λ a → auditWatchFrom (acc ∨ reportsLoss q a) (k a)
  auditWatchFrom acc (coin μ k) = coin μ λ b → auditWatchFrom acc (k b)

  auditWatch : Strat Query Answer → Strat Query Answer
  auditWatch = auditWatchFrom false

  -- It asks exactly what `d` asks, so it costs the budget nothing.
  asks≤-auditWatch : (n : ℕ) (acc : Bool) (d : Strat Query Answer)
                   → asks≤ n d → asks≤ n (auditWatchFrom acc d)
  asks≤-auditWatch _       _   (out _)    _ = tt
  asks≤-auditWatch zero    _   (ask _ _)  a = a
  asks≤-auditWatch (suc n) acc (ask q k)  a = λ r → asks≤-auditWatch n _ (k r) (a r)
  asks≤-auditWatch n       acc (coin _ k) a = λ b → asks≤-auditWatch n acc (k b) (a b)

TrajectoryLossBounded AuditLossBounded : Variant → LState → (ℕ → ℚ) → Set
TrajectoryLossBounded vr s₀ = BoundedHit (Sys vr s₀) (badTotal s₀)
AuditLossBounded      vr s₀ = Bounded    (Sys vr s₀) (auditWatch s₀)

-- `d` with an audit after every answer: the invariant is queried at exactly
-- the activation boundaries the trajectory inspects.
withAudits : Strat Query Answer → Strat Query Answer
withAudits (out b)    = out b
withAudits (ask q k)  = ask q λ a → ask audit λ _ → withAudits (k a)
withAudits (coin μ k) = coin μ λ b → withAudits (k b)

-- …and what that instrumentation costs an allowance: one extra ask per
-- answer, so the ask-depth doubles.
asks≤-withAudits : (n : ℕ) (d : Strat Query Answer) → asks≤ n d → asks≤ (n +ᴺ n) (withAudits d)
asks≤-withAudits _       (out _)    _ = tt
asks≤-withAudits (suc n) (ask _ k)  a = λ r →
  subst (λ m → asks≤ m (ask audit λ _ → withAudits (k r))) (sym (+-suc n n))
        λ _ → asks≤-withAudits n (k r) (a r)
asks≤-withAudits n       (coin _ k) a = λ b → asks≤-withAudits n (k b) (a b)

------------------------------------------------------------------------
-- The audit answer is truthful
------------------------------------------------------------------------

-- Nothing below reads the hash implementation: an audit query is answered
-- from the ledger's own state (`served`) and the trajectory event ignores the
-- second component, so the argument is the same at the random oracle and at
-- any real hash.
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

    -- The genesis state is not itself a violation, so the run starts clear.
    init-good : Bad (s₀ , init hash) ≡ false
    init-good = cong not (Equivalence.to T-≡ (≡⇒≡ᵇ (total s₀) (total s₀) refl))

  -- Both directions run at any two accumulators the first of which is behind:
  -- the Boolean order carries "behind" through the induction, which is what an
  -- accumulating watch needs in place of a separate monotonicity lemma.
  sound : {acc acc′ : Bool} → acc ≤ᵇ acc′ → (st : St P) (d : Strat Query Answer)
        → Pr₁⊥ (runFrom P st (auditWatchFrom s₀ acc d))
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
    Lb b = runFrom P st (auditWatchFrom s₀ acc (k b))
    Rb b = hitFrom P Bad acc′ st (k b)
  sound {acc} {acc′} le st (ask (submit tx) k) =
    ≤-trans (≤-reflexive (E⊥-bind μq L bool→ℚ))
    (≤-trans (E⊥-mono μq (λ x → Pr₁⊥ (L x)) (λ x → Pr₁⊥ (R x)) ptw)
             (≤-reflexive (sym (E⊥-bind μq R bool→ℚ))))
    where
    μq = kernel P st (submit tx)

    L R : St P × Answer → Dist⊥ Bool
    L (st′ , r) = runFrom P st′ (auditWatchFrom s₀ (acc ∨ false) (k r))
    R (st′ , r) = hitFrom P Bad (acc′ ∨ Bad st′) st′ (k r)

    ptw : (x : St P × Answer) → Pr₁⊥ (L x) ≤ℚ Pr₁⊥ (R x)
    ptw (st′ , r) = sound (∨-mono le (≤-minimum (Bad st′))) st′ (k r)
  sound {acc} {acc′} le (s , tbl) (ask audit k) =
    ≤-trans (≤-reflexive (served (s , tbl) L))
    (≤-trans (sound (∨-mono le b≤b) (s , tbl) (k (totalIs (total s))))
             (≤-reflexive (sym (served (s , tbl) R))))
    where
    L R : St P × Answer → Dist⊥ Bool
    L (st′ , r) = runFrom P st′ (auditWatchFrom s₀ (acc ∨ lostValue s₀ r) (k r))
    R (st′ , r) = hitFrom P Bad (acc′ ∨ Bad st′) st′ (k r)

  -- Every state the trajectory inspects is audited at the boundary it is
  -- inspected, and the audit answer there is `Bad`, so no case on the query is
  -- needed — what the watch reads of `d`'s own answers can only help.
  complete : {acc acc′ : Bool} → acc ≤ᵇ acc′ → (st : St P) (d : Strat Query Answer)
           → Pr₁⊥ (hitFrom P Bad acc st d)
             ≤ℚ Pr₁⊥ (runFrom P st (auditWatchFrom s₀ acc′ (withAudits d)))
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
    Rb b = runFrom P st (auditWatchFrom s₀ acc′ (withAudits (k b)))
  complete {acc} {acc′} le st (ask q k) =
    ≤-trans (≤-reflexive (E⊥-bind μq H bool→ℚ))
    (≤-trans (E⊥-mono μq (λ x → Pr₁⊥ (H x)) (λ x → Pr₁⊥ (R x)) ptw)
             (≤-reflexive (sym (E⊥-bind μq R bool→ℚ))))
    where
    μq = kernel P st q

    H R : St P × Answer → Dist⊥ Bool
    H (st′ , r) = hitFrom P Bad (acc ∨ Bad st′) st′ (k r)
    R (st′ , r) = runFrom P st′
      (auditWatchFrom s₀ (acc′ ∨ reportsLoss s₀ q r) (ask audit λ _ → withAudits (k r)))

    -- What the injected audit query leads to, whatever it finds.
    after : (r : Answer) → St P × Answer → Dist⊥ Bool
    after r (st″ , a) = runFrom P st″
      (auditWatchFrom s₀ ((acc′ ∨ reportsLoss s₀ q r) ∨ lostValue s₀ a) (withAudits (k r)))

    ptw : (x : St P × Answer) → Pr₁⊥ (H x) ≤ℚ Pr₁⊥ (R x)
    ptw (st′ , r) =
      ≤-trans (complete (∨-mono (∨-monoʳ le) b≤b) st′ (k r))
              (≤-reflexive (sym (served st′ (after r))))

  auditWatch-sound : (d : Strat Query Answer) → Pr P (auditWatch s₀ d) ≤ℚ PrHit P Bad d
  auditWatch-sound d =
    subst (λ b → Pr₁⊥ (runFrom P (s₀ , init hash) (auditWatch s₀ d))
                 ≤ℚ Pr₁⊥ (hitFrom P Bad b (s₀ , init hash) d))
          (sym init-good) (sound b≤b (s₀ , init hash) d)

  auditWatch-complete : (d : Strat Query Answer)
                      → PrHit P Bad d ≤ℚ Pr P (auditWatch s₀ (withAudits d))
  auditWatch-complete d =
    subst (λ b → Pr₁⊥ (hitFrom P Bad b (s₀ , init hash) d)
                 ≤ℚ Pr₁⊥ (runFrom P (s₀ , init hash) (auditWatch s₀ (withAudits d))))
          (sym init-good) (complete b≤b (s₀ , init hash) d)

-- The honesty pin: at the random oracle a trajectory bound BECOMES the
-- watch's bound, with no hypothesis added along the way.
auditWatch-bounded : (vr : Variant) (s₀ : LState) {ε : ℕ → ℚ}
                   → TrajectoryLossBounded vr s₀ ε → AuditLossBounded vr s₀ ε
auditWatch-bounded vr s₀ bnd q d a =
  ≤-trans (auditWatch-sound oracle vr s₀ d) (bnd q d a)
