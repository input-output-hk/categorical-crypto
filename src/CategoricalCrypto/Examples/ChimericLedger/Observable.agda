{-# OPTIONS --safe --without-K #-}

-- `auditWatch-sound` and `auditWatch-complete` tie the audit watch to the
-- state-trajectory event; both are plain inductions because an audit answer is
-- definitionally the audited state's total.
--
-- The watch accumulates instead of stopping at the first violation: an early
-- `out true` weighs 1 where the continued run may deadlock and weigh nothing,
-- which would break `auditWatch-sound`.

open import Data.Bool.Base renaming (_≤_ to _≤ᵇ_)
open import Data.Bool.Properties using (T-≡; ≤-minimum)
open import Data.Bool.Properties.Ext
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ᴺ_; _≡ᵇ_ to _≡ᴺ_)
open import Data.Nat.Properties using (+-suc; ≡⇒≡ᵇ)
open import Data.Product.Base
open import Data.Rational using (ℚ) renaming (_≤_ to _≤ℚ_)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Data.Unit.Base
open import Function.Bundles
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
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

badTotal : {S : Set} → LState → LState × S → Bool
badTotal s₀ st = not (total (proj₁ st) ≡ᴺ total s₀)

module _ (t₀ : ℕ) where

  lostValue : Answer → Bool
  lostValue (ok _)      = false
  lostValue (totalIs t) = not (t ≡ᴺ t₀)

  reportsLoss : Query → Answer → Bool
  reportsLoss (submit _) _ = false
  reportsLoss audit      a = lostValue a

  auditWatchFrom : Bool → Strat Query Answer → Strat Query Answer
  auditWatchFrom = watchFrom reportsLoss

  auditWatch : Strat Query Answer → Strat Query Answer
  auditWatch = auditWatchFrom false

TrajectoryLossBounded AuditLossBounded : Variant → LState → (ℕ → ℚ) → Set
TrajectoryLossBounded vr s₀ = BoundedHit (Sys vr s₀) (badTotal s₀)
AuditLossBounded      vr s₀ = Bounded    (Sys vr s₀) (auditWatch (total s₀))

-- An audit after every answer: exactly the boundaries `hitFrom` inspects.
withAudits : Strat Query Answer → Strat Query Answer
withAudits (out b)    = out b
withAudits (ask q k)  = ask q λ a → ask audit λ _ → withAudits (k a)
withAudits (coin μ k) = coin μ λ b → withAudits (k b)

asks≤-withAudits : (n : ℕ) (d : Strat Query Answer) → asks≤ n d → asks≤ (n +ᴺ n) (withAudits d)
asks≤-withAudits _       (out _)    _ = tt
asks≤-withAudits (suc n) (ask _ k)  a = λ r →
  subst (λ m → asks≤ m (ask audit λ _ → withAudits (k r))) (sym (+-suc n n))
        λ _ → asks≤-withAudits n (k r) (a r)
asks≤-withAudits n       (coin _ k) a = λ b → asks≤-withAudits n (k b) (a b)

------------------------------------------------------------------------
-- The audit answer is truthful
------------------------------------------------------------------------

module _ (hash : Protocol unitᴵ HashIf) (vr : Variant) (s₀ : LState) where

  private
    P = Sysᴴ hash vr s₀

    Bad : St P → Bool
    Bad = badTotal s₀

    t₀ : ℕ
    t₀ = total s₀

    verdict : (b : Bool) → Pr₁⊥ (return⊥ b) ≡ bool→ℚ b
    verdict b = lookupᴰℚ-return (just b) mb

    served : (st : St P) (G : St P × Answer → Dist⊥ Bool)
           → Pr₁⊥ (kernel P st audit >>=⊥ G)
             ≡ Pr₁⊥ (G (st , totalIs (total (proj₁ st))))
    served st G = Pr₁⊥-cong (kernel P st audit >>=⊥ G)
                            (G (st , totalIs (total (proj₁ st))))
                            (>>=⊥-identityˡ (st , totalIs (total (proj₁ st))) G)

    init-good : Bad (s₀ , init hash) ≡ false
    init-good = cong not (Equivalence.to T-≡ (≡⇒≡ᵇ (total s₀) (total s₀) refl))

  -- Both directions run at any two accumulators the first of which is behind:
  -- the Boolean order carries "behind" through the induction, which is what an
  -- accumulating watch needs in place of a separate monotonicity lemma.
  sound : {acc acc′ : Bool} → acc ≤ᵇ acc′ → (st : St P) (d : Strat Query Answer)
        → Pr₁⊥ (runFrom P st (auditWatchFrom t₀ acc d))
          ≤ℚ Pr₁⊥ (hitFrom P Bad acc′ st d)
  sound b≤b _  (out _) = ≤-refl
  sound f≤t _  (out _) =
    ≤-trans (≤-reflexive (verdict false)) (≤-trans 0≤1ℚ (≤-reflexive (sym (verdict true))))
  sound {acc} {acc′} le st (coin μ k) =
    Pr₁⊥-bindᴹ-mono μ (λ b → runFrom P st (auditWatchFrom t₀ acc (k b)))
                      (λ b → hitFrom P Bad acc′ st (k b)) (λ b → sound le st (k b))
  sound {acc} {acc′} le st (ask (submit tx) k) = Pr₁⊥-bind-mono (kernel P st (submit tx)) L R ptw
    where
    L R : St P × Answer → Dist⊥ Bool
    L (st′ , r) = runFrom P st′ (auditWatchFrom t₀ (acc ∨ false) (k r))
    R (st′ , r) = hitFrom P Bad (acc′ ∨ Bad st′) st′ (k r)

    ptw : (x : St P × Answer) → Pr₁⊥ (L x) ≤ℚ Pr₁⊥ (R x)
    ptw (st′ , r) = sound (∨-mono-≤ le (≤-minimum (Bad st′))) st′ (k r)
  sound {acc} {acc′} le (s , tbl) (ask audit k) =
    ≤-trans (≤-reflexive (served (s , tbl) L))
    (≤-trans (sound (∨-mono-≤ le b≤b) (s , tbl) (k (totalIs (total s))))
             (≤-reflexive (sym (served (s , tbl) R))))
    where
    L R : St P × Answer → Dist⊥ Bool
    L (st′ , r) = runFrom P st′ (auditWatchFrom t₀ (acc ∨ lostValue t₀ r) (k r))
    R (st′ , r) = hitFrom P Bad (acc′ ∨ Bad st′) st′ (k r)

  -- Every state the trajectory inspects is audited at the boundary it is
  -- inspected, and the audit answer there is `Bad`, so no case on the query is
  -- needed — what the watch reads of `d`'s own answers can only help.
  complete : {acc acc′ : Bool} → acc ≤ᵇ acc′ → (st : St P) (d : Strat Query Answer)
           → Pr₁⊥ (hitFrom P Bad acc st d)
             ≤ℚ Pr₁⊥ (runFrom P st (auditWatchFrom t₀ acc′ (withAudits d)))
  complete b≤b _  (out _) = ≤-refl
  complete f≤t _  (out _) =
    ≤-trans (≤-reflexive (verdict false)) (≤-trans 0≤1ℚ (≤-reflexive (sym (verdict true))))
  complete {acc} {acc′} le st (coin μ k) =
    Pr₁⊥-bindᴹ-mono μ (λ b → hitFrom P Bad acc st (k b))
                      (λ b → runFrom P st (auditWatchFrom t₀ acc′ (withAudits (k b))))
                      (λ b → complete le st (k b))
  complete {acc} {acc′} le st (ask q k) = Pr₁⊥-bind-mono (kernel P st q) H R ptw
    where
    H R : St P × Answer → Dist⊥ Bool
    H (st′ , r) = hitFrom P Bad (acc ∨ Bad st′) st′ (k r)
    R (st′ , r) = runFrom P st′
      (auditWatchFrom t₀ (acc′ ∨ reportsLoss t₀ q r) (ask audit λ _ → withAudits (k r)))

    after : (r : Answer) → St P × Answer → Dist⊥ Bool
    after r (st″ , a) = runFrom P st″
      (auditWatchFrom t₀ ((acc′ ∨ reportsLoss t₀ q r) ∨ lostValue t₀ a) (withAudits (k r)))

    ptw : (x : St P × Answer) → Pr₁⊥ (H x) ≤ℚ Pr₁⊥ (R x)
    ptw (st′ , r) =
      ≤-trans (complete (∨-mono-≤ (a≤b⇒a≤b∨c le) b≤b) st′ (k r))
              (≤-reflexive (sym (served st′ (after r))))

  auditWatch-sound : (d : Strat Query Answer) → Pr P (auditWatch (total s₀) d) ≤ℚ PrHit P Bad d
  auditWatch-sound d =
    subst (λ b → Pr₁⊥ (runFrom P (s₀ , init hash) (auditWatch t₀ d))
                 ≤ℚ Pr₁⊥ (hitFrom P Bad b (s₀ , init hash) d))
          (sym init-good) (sound b≤b (s₀ , init hash) d)

  auditWatch-complete : (d : Strat Query Answer)
                      → PrHit P Bad d ≤ℚ Pr P (auditWatch (total s₀) (withAudits d))
  auditWatch-complete d =
    subst (λ b → Pr₁⊥ (hitFrom P Bad b (s₀ , init hash) d)
                 ≤ℚ Pr₁⊥ (runFrom P (s₀ , init hash) (auditWatch t₀ (withAudits d))))
          (sym init-good) (complete b≤b (s₀ , init hash) d)

auditWatch-bounded : (vr : Variant) (s₀ : LState) {ε : ℕ → ℚ}
                   → TrajectoryLossBounded vr s₀ ε → AuditLossBounded vr s₀ ε
auditWatch-bounded vr s₀ bnd q d a = ≤-trans (auditWatch-sound oracle vr s₀ d) (bnd q d a)
