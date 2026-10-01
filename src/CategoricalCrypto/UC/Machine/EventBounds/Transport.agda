{-# OPTIONS --safe --without-K --guardedness #-}

-- Transporting an event bound from an ideal to a real closed process along a
-- one-sided comparison of their strategy-level runs (`Near`), for any reader
-- with an adequacy pair (`docs/state-event-transport-spike.md`).

open import Algebra.Bundles
open import Data.Bool.Base
open import Data.Nat.Base as ℕ
open import Data.Nat.Poly
open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties
open import Function.Base

import Data.Nat.Properties as ℕP
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import Algebra.Properties.CommutativeSemigroup (CommutativeMonoid.commutativeSemigroup +-0-commutativeMonoid)

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.EventBounds
open import CategoricalCrypto.UC.Machine.Monitor
open import CategoricalCrypto.UC.Machine.Monitor.Agree
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Machine.StateEvent
open import CategoricalCrypto.UC.Machine.StateEvent.Agree
open import CategoricalCrypto.UC.Machine.StateEvent.Lift
open import CategoricalCrypto.UC.Machine.StateEvent.Read
open import CategoricalCrypto.UC.Model.Family.Emulation
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.Quantitative.EventLift

module CategoricalCrypto.UC.Machine.EventBounds.Transport where

private variable
  A B B′ : Iface
  u : Proc unitᴵ B′
  q : ℕ
  r ε : ℚ

------------------------------------------------------------------------
-- The schema

-- Only `true`'s mass is compared, cofinally: every real depth is dominated by
-- some ideal depth up to `ε`.
Near : (Strat (Neg B) (Pos B) → Strat (Neg B′) (Pos B′)) → ℕ → ℚ → (R I : Proc unitᴵ B′) → Set
Near {B} τ q ε R I = (d : Strat (Neg B) (Pos B)) → asks≤ q d → Dom (indᵇ true) ε (runᴹ R (τ d)) (runᴹ I (τ d))

-- The adequacy pair is two premises (`Lifts`, `Agrees`), not a record: a
-- record packaging them exhausts an 8 GiB heap at its declaration.
module _ (𝔠 : Reader B B′) (τ : Strat (Neg B) (Pos B) → Strat (Neg B′) (Pos B′)) where

  -- `cap q` is the strategy allowance the lift needs at context cap `q`.
  Lifts : (ℕ → ℕ) → Proc unitᴵ B′ → Set₁
  Lifts cap u = (q : ℕ) {r : ℚ}
              → ((d : Strat (Neg B) (Pos B)) → asks≤ (cap q) d → Upper (runᴹ u (τ d)) r) → BoundedAt q r u 𝔠

  Agrees : Proc unitᴵ B′ → Set
  Agrees u = (d : Strat (Neg B) (Pos B)) → readRun unitᴵ u 𝔠 (stratTest B d) m₀ ≈ₚ runᴹ u (τ d)

  -- The converse of a lift, at the embedded strategy: nothing is spent.
  unlift : Agrees u → BoundedAt q r u 𝔠 → (d : Strat (Neg B) (Pos B)) → asks≤ q d → Upper (runᴹ u (τ d)) r
  unlift {q = q} ag h d a = upper-≈ (≈ₚ-sym _ _ (ag d))
    (h unitᴵ (stratTest B d) m₀ (qb-stratTest B d a) (qb-closed m₀) (ℕP.≤-reflexive (scale-unit q)))

  transport : {cap : ℕ → ℕ} {R I : Proc unitᴵ B′} → Lifts cap R → Agrees I
            → Near τ (cap q) ε R I → BoundedAt (cap q) r I 𝔠 → BoundedAt q (r ℚ.+ ε) R 𝔠
  transport {q = q} lf ag near h = lf q λ d a → upper-dom (near d a) (unlift ag h d a)

module _ {B B′ : ℕ → Iface} (𝔠 : (n : ℕ) → Reader (B n) (B′ n))
         (τ : (n : ℕ) → Strat (Neg (B n)) (Pos (B n)) → Strat (Neg (B′ n)) (Pos (B′ n)))
         {cap : ℕ → ℕ} {R I : (n : ℕ) → Proc unitᴵ (B′ n)} {δ εI : ℕ → ℕ → ℚ}
         (lf : (n : ℕ) → Lifts (𝔠 n) (τ n) cap (R n)) (ag : (n : ℕ) → Agrees (𝔠 n) (τ n) (I n))
         (near : (n q : ℕ) → Near (τ n) (cap q) (δ n q) (R n) (I n)) where

  transportᶠ : Boundedᶠ I 𝔠 εI → Boundedᶠ R 𝔠 (λ n q → εI n (cap q) ℚ.+ δ n q)
  transportᶠ h n q = transport (𝔠 n) (τ n) (lf n) (ag n) (near n q) (h n (cap q))

  transportᴺ : ({p : ℕ → ℕ} → Poly p → Poly (cap ∘ p))
             → Boundedᴺ I 𝔠 εI → Boundedᴺ R 𝔠 (λ n q → εI n (cap q) ℚ.+ δ n q)
  transportᴺ pc h p pp = let ν , nν , b = h (cap ∘ p) (pc pp) in ν , nν , λ n Y E m qE qm le →
    upper-mono (≤-reflexive (xy∙z≈xz∙y (εI n (cap (p n))) (ν n) (δ n (p n))))
      (transport (𝔠 n) (τ n) (lf n) (ag n) (near n (p n)) (b n) Y E m qE qm le)

------------------------------------------------------------------------
-- The flag wire

FlagNear : ℕ → ℚ → (R : Proc unitᴵ B) → StateTest R → (I : Proc unitᴵ B) → StateTest I → Set
FlagNear {B} q ε R P I Q = Near flagStrat q ε (R ▷ P) (I ▷ Q)

transport-near : {R I : Proc unitᴵ B} {P : StateTest R} {Q : StateTest I}
               → FlagNear q ε R P I Q → StateBoundedAt q r I Q → StateBoundedAt q (r ℚ.+ ε) R P
transport-near {B} {R = R} {I} {P} {Q} = transport (flagReader B) flagStrat (stateLift R P) (stateRead-agree I Q)

-- Exact, at any `A`.
transportᵉ : {R I : Proc A B} {P : StateTest R} {Q : StateTest I}
           → EventSim (R , P) (I , Q) → StateBoundedAt q r I Q → StateBoundedAt q r R P
transportᵉ e = stateBounded-resp-≈ᵉ (EqC.symmetric EventSim (EqC.return e))

eventSim⇒near : {R I : Proc unitᴵ B} {P : StateTest R} {Q : StateTest I}
              → EventSim (R , P) (I , Q) → FlagNear q 0ℚ R P I Q
eventSim⇒near e d _ = proj₁ (≈ₚ⇒≈ₚ[0] (runᴹ-resp-≈ᴹ (S.≲⇒≈ᴹ (▷-≲ e)) (flagStrat d))) true

-- `_≈ᶠ[_]_` compares protocol images, and `R ▷ P` is not one, so the premise
-- names flagged realizations `FR`/`FI` of the two flagged machines.
module _ {B : ℕ → Iface} (R I : Systems B)
         (P : (n : ℕ) → StateTest (morphism (R n))) (Q : (n : ℕ) → StateTest (morphism (I n)))
         (FR FI : Systems (λ n → B n ⊗ᴵ Ωᴵ))
         (rR : (n : ℕ) → morphism (FR n) S.≈ᴹ (morphism (R n) ▷ P n))
         (rI : (n : ℕ) → morphism (FI n) S.≈ᴹ (morphism (I n) ▷ Q n)) where

  -- The flag ask is one more query: the error is read at allowance `q + 1`.
  flagged-near : (ε : ℕ → ℕ → ℚ) → FR ≈ᶠ[ ε ] FI
               → (n q : ℕ) → FlagNear q (ε n (suc q)) (morphism (R n)) (P n) (morphism (I n)) (Q n)
  flagged-near ε h n q d a =
    proj₁ (≈ₚ[]-resp (runᴹ-resp-≈ᴹ (rR n) (flagStrat d)) (runᴹ-resp-≈ᴹ (rI n) (flagStrat d))
                     (≈ᶠ-runs ε h n (suc q , s≤s z≤n) (flagStrat d) (asks≤-flag q d a))) true

  flagged-transport : (εI ε : ℕ → ℕ → ℚ) → FR ≈ᶠ[ ε ] FI
                    → StateBoundedᶠ (λ n → morphism (I n)) Q εI
                    → StateBoundedᶠ (λ n → morphism (R n)) P (λ n q → εI n q ℚ.+ ε n (suc q))
  flagged-transport εI ε h =
    transportᶠ (flagReader ∘ B) (λ _ → flagStrat) (λ n → stateLift (morphism (R n)) (P n))
               (λ n → stateRead-agree (morphism (I n)) (Q n)) (flagged-near ε h)

------------------------------------------------------------------------
-- The compiled monitor

hitsTransport : (report : Neg B → Pos B → Bool) {R I : Proc unitᴵ B}
              → Near (watchFrom report false) q ε R I
              → HitsAt q r I (monitorᴹ report) → HitsAt q (r ℚ.+ ε) R (monitorᴹ report)
hitsTransport {q = q} report {R} {I} near h =
  hitsᵘ report R q λ d a → upper-dom (near d a) (hits⇒upper report I q h d a)

hitsTransportᴺ : {B : ℕ → Iface} (report : (n : ℕ) → Neg (B n) → Pos (B n) → Bool)
                 {R I : (n : ℕ) → Proc unitᴵ (B n)} {δ εI : ℕ → ℕ → ℚ}
               → ((n q : ℕ) → Near (watchFrom (report n) false) q (δ n q) (R n) (I n))
               → Hitsᴺ I (monitorᴹ ∘ report) εI
               → Hitsᴺ R (monitorᴹ ∘ report) (λ n q → εI n q ℚ.+ δ n q)
hitsTransportᴺ report {δ = δ} {εI} near h p pp =
  let ν , nν , b = h p pp in ν , nν , λ n Y E m qE qm le →
    upper-mono (≤-reflexive (xy∙z≈xz∙y (εI n (p n)) (ν n) (δ n (p n))))
      (hitsTransport (report n) (near n (p n)) (b n) Y E m qE qm le)
