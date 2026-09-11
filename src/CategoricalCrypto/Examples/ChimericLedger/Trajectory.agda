{-# OPTIONS --safe --without-K #-}

-- `TrajectoryFromAudit`, proved: the trajectory statement is the audit-form
-- statement, on the audit-interleaved strategy.
--
-- `audited d` asks `audit` after EVERY answer, so every state the trajectory
-- observable inspects is audited at the boundary it is inspected.  Two facts
-- make the comparison an induction with nothing else in it: an audit answer is
-- definitionally the truth about the state it is asked at
-- (`step (Sys …) (s , tbl) audit = ret ((s , tbl) , totalIs (total s))`), and
-- `watch`'s test on that answer is literally `badTotal`'s.  So no persistence
-- argument is needed — `hitFrom`'s accumulator and `watch`'s early `out true`
-- fire at exactly the same boundaries, and the extra chances `watch` takes on
-- the strategy's OWN audit queries only help the inequality.

open import Data.Bool.Base using (Bool; true; false; not; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Data.List.Base using (List; [])
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ) renaming (_≡ᵇ_ to _≡ᴺ_)
open import Data.Nat.Properties using (≡⇒≡ᵇ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational using (1ℚ) renaming (_≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Prelude
open import ProbabilisticLogic.Distribution.RationalDist using (lookupᴰℚ-return)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using
  (E-bind; E-mono; E⊥-bind; E⊥-mono; Pr₁⊥≤1)
open import ProbabilisticLogic.Distribution.Uniform using (bool→ℚ)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Examples.ChimericLedger.Trajectory
  (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) where

open Ledger ℓ

open import CategoricalCrypto.Examples.ChimericLedger.POV ℓ ser

module _ (vr : Variant) (s₀ : LState) where

  private
    P = Sys vr s₀

    Bad : St P → Bool
    Bad = badTotal s₀

    -- `watch` answers `true` outright, whatever the state.
    out-true : (st : St P) → Pr₁⊥ (runFrom P st (out true)) ≡ 1ℚ
    out-true st = lookupᴰℚ-return (just true) mb

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
      μq = evalC (step P st q)

      H R : St P × Answer → Dist⊥ Bool
      H (st′ , r) = hitFrom P Bad (Bad st′) st′ (k r)
      R (st′ , r) = runFrom P st′
        (if violates s₀ r then out true else watch s₀ (ask audit λ _ → audited (k r)))

      ptw : (x : St P × Answer) → Pr₁⊥ (H x) ≤ℚ Pr₁⊥ (R x)
      ptw (st′ , r) with violates s₀ r
      ... | true  = ≤-trans (Pr₁⊥≤1 (hitFrom P Bad (Bad st′) st′ (k r)))
                            (≤-reflexive (sym (out-true st′)))
      ... | false = auditStep st′ (k r)

    -- The audit query itself: it does not move the state, and its answer is
    -- the state's own `total`, so `watch`'s test on it IS `Bad`.
    auditStep : (st : St P) (c : Strat Query Answer)
              → Pr₁⊥ (hitFrom P Bad (Bad st) st c)
                ≤ℚ Pr₁⊥ (runFrom P st (watch s₀ (ask audit λ _ → audited c)))
    auditStep (s , tbl) c = ≤-trans body (≤-reflexive (sym served))
      where
      G : St P × Answer → Dist⊥ Bool
      G (st′ , r) = runFrom P st′
        (if violates s₀ r then out true else watch s₀ (audited c))

      served : Pr₁⊥ (runFrom P (s , tbl) (watch s₀ (ask audit λ _ → audited c)))
             ≡ Pr₁⊥ (G ((s , tbl) , totalIs (total s)))
      served = Pr₁⊥-cong (runFrom P (s , tbl) (watch s₀ (ask audit λ _ → audited c)))
                         (G ((s , tbl) , totalIs (total s)))
                         (>>=⊥-identityˡ ((s , tbl) , totalIs (total s)) G)

      body : Pr₁⊥ (hitFrom P Bad (Bad (s , tbl)) (s , tbl) c)
           ≤ℚ Pr₁⊥ (G ((s , tbl) , totalIs (total s)))
      body with total s ≡ᴺ total s₀
      ... | true  = core (s , tbl) c
      ... | false = ≤-trans (Pr₁⊥≤1 (hitFrom P Bad true (s , tbl) c))
                            (≤-reflexive (sym (out-true (s , tbl))))

  -- The genesis state is not itself a violation, so the run starts clear.
  private
    init-good : Bad (s₀ , []) ≡ false
    init-good = cong not (Equivalence.to T-≡ (≡⇒≡ᵇ (total s₀) (total s₀) refl))

  trajectoryFromAudit : TrajectoryFromAudit vr s₀
  trajectoryFromAudit d =
    subst (λ b → Pr₁⊥ (hitFrom P Bad b (s₀ , []) d)
                 ≤ℚ Pr₁⊥ (runFrom P (s₀ , []) (watch s₀ (audited d))))
          (sym init-good) (core (s₀ , []) d)
