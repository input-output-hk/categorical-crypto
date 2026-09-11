{-# OPTIONS --safe --without-K #-}

-- The chimeric ledger over a random oracle, and preservation of value.
--
--     oracle : Protocol unitᴵ HashIf            -- the hash functionality
--     ledger : Protocol HashIf LedgerIf         -- the plain-Agda protocol
--     Sys    = ledger ∘ᵖ oracle                 -- the closed system
--
-- `POV` is the target statement, over the STATE TRAJECTORY: no strategy of
-- query budget `q` reaches a ledger state whose total value differs from the
-- initial one, except with probability `ε q`.  It is deliberately not phrased
-- over the ledger's own audit answers — that form would trust the ledger to
-- report honestly.  The audit form survives below as the gadget the transfer
-- lemma applies to, and as `monitor`, the observable the UC layer's audit
-- event designates; that the audit answer may be trusted is
-- `ChimericLedger.Trajectory`'s theorem rather than an assumption of the
-- statement.

open import Class.DecEq

open import Data.Bool.Base
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base renaming (_+_ to _+ᴺ_; _*_ to _*ᴺ_; _≡ᵇ_ to _≡ᴺ_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base
open import Data.Rational renaming (_+_ to _+ℚ_; _≤_ to _≤ℚ_)
open import Data.Rational.Properties
open import Function.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Prelude

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Examples.RandomOracle
open import CategoricalCrypto.Iface
open import CategoricalCrypto.OracleCall
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Examples.ChimericLedger.POV
  (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) where

open Ledger ℓ
open Step ser

-- One party, hashing BITSTRINGS to ℓ bits: keying the oracle on `Tx` would
-- hide the serialization.
module RO = RandomOracle 1 (List Bool) ℓ

------------------------------------------------------------------------
-- The interfaces and the two components
------------------------------------------------------------------------

data Query : Set where
  submit : Tx → Query
  audit  : Query

data Answer : Set where
  ok      : Bool → Answer
  totalIs : ℕ → Answer

HashIf LedgerIf : Iface
HashIf   = RO.Output ⇿ RO.Input
LedgerIf = Answer ⇿ Query

-- The lazily sampled random oracle: repeats from the table, fresh answers one
-- fair coin per bit (`RandomOracle.step`'s distribution, as a call tree).
oracle : Protocol unitᴵ HashIf
oracle = record { St = RO.Table ; init = [] ; step = go }
  where
    go : RO.Table → RO.Input → Calls unitᴵ (RO.Table × RO.Output)
    go tbl (i , q) = case RO.lookup-bs tbl q of λ where
      (just h) → ret (tbl , (i , h))
      nothing  → uniformVec ℓ λ h → ret ((q , h) ∷ tbl , (i , h))

-- `submit` serializes and calls; `audit` answers purely.  `reCall` tags the
-- query and drops the party index from the reply, `mapCall` wraps the
-- acceptance bit.
ledger : Variant → LState → Protocol HashIf LedgerIf
ledger vr s₀ = record { St = LState ; init = s₀ ; step = go }
  where
    go : LState → Query → Calls HashIf (LState × Answer)
    go s (submit tx) = fromCall (reCall (fzero ,_) proj₂
      (mapCall (λ sb → proj₁ sb , ok (proj₂ sb)) (applyTx vr s tx)))
    go s audit       = ret (s , totalIs (total s))

-- The ledger over an ARBITRARY hash implementation: the shape of the real side
-- of a UC statement whose ideal side is `Sys` — the same ledger code, with the
-- random oracle in place of the implementation.
Sysᴴ : Protocol unitᴵ HashIf → Variant → LState → Protocol unitᴵ LedgerIf
Sysᴴ hash vr s₀ = ledger vr s₀ ∘ᵖ hash

Sys : Variant → LState → Protocol unitᴵ LedgerIf
Sys = Sysᴴ oracle

------------------------------------------------------------------------
-- The statement
------------------------------------------------------------------------

-- The system's state is the two components'; the ledger's is the first, and
-- the hash implementation's — whatever it holds — is not read at all.
badTotal : {S : Set} → LState → LState × S → Bool
badTotal s₀ st = not (total (proj₁ st) ≡ᴺ total s₀)

POV : Variant → LState → (ℕ → ℚ) → Set
POV vr s₀ = BoundedHit (Sys vr s₀) (badTotal s₀)

------------------------------------------------------------------------
-- The audit-form gadget
------------------------------------------------------------------------

-- `watch` depends only on the audited invariant, so both variants are watched
-- by the same transformation.
module _ (s₀ : LState) where

  violates : Answer → Bool
  violates (ok _)      = false
  violates (totalIs t) = not (t ≡ᴺ total s₀)

  watch : Strat Query Answer → Strat Query Answer
  watch (out _)    = out false
  watch (ask q k)  = ask q λ a → if violates a then out true else watch (k a)
  watch (coin μ k) = coin μ λ b → watch (k b)

  private
    stop : (n : ℕ) (b : Bool) (d : Strat Query Answer)
         → asks≤ n d → asks≤ n (if b then out true else d)
    stop _ true  _ _ = tt
    stop _ false _ a = a

  asks≤-watch : (n : ℕ) (d : Strat Query Answer) → asks≤ n d → asks≤ n (watch d)
  asks≤-watch _       (out _)    _ = tt
  asks≤-watch zero    (ask _ _)  a = a
  asks≤-watch (suc n) (ask _ k)  a =
    λ r → stop n (violates r) (watch (k r)) (asks≤-watch n (k r) (a r))
  asks≤-watch n       (coin _ k) a = λ b → asks≤-watch n (k b) (a b)

  -- The TRUSTED reading of an answer: a `totalIs` answer is the audited state's
  -- own total (`ChimericLedger.Trajectory`), so it may be believed; nothing
  -- makes a `submit` acknowledgement a report about the state, so it is not
  -- read at all.  Which query was asked is what distinguishes the two, and that
  -- is why the monitor below reads the query alongside the answer.
  violatesAt : Query → Answer → Bool
  violatesAt (submit _) _ = false
  violatesAt audit      a = violates a

  -- The monitor whose verdict is the designated audit event: `d` played
  -- unchanged, its audit answers accumulated, the verdict reported where `d`
  -- reports its own.  `watch` above stops at the first violation instead, which
  -- costs it soundness against the trajectory — an early `out true` weighs 1
  -- where the continued run may deadlock and weigh nothing — so it is the
  -- accumulating form that an ideal trajectory bound can supply
  -- (`Trajectory.monitor-sound`, `docs/protocol-implementation-review.md` §1).
  monitorFrom : Bool → Strat Query Answer → Strat Query Answer
  monitorFrom acc (out _)    = out acc
  monitorFrom acc (ask q k)  = ask q λ a → monitorFrom (acc ∨ violatesAt q a) (k a)
  monitorFrom acc (coin μ k) = coin μ λ b → monitorFrom acc (k b)

  monitor : Strat Query Answer → Strat Query Answer
  monitor = monitorFrom false

  -- The monitor asks exactly what `d` asks, so it costs the budget nothing.
  asks≤-monitor : (n : ℕ) (acc : Bool) (d : Strat Query Answer)
                → asks≤ n d → asks≤ n (monitorFrom acc d)
  asks≤-monitor _       _   (out _)    _ = tt
  asks≤-monitor zero    _   (ask _ _)  a = a
  asks≤-monitor (suc n) acc (ask q k)  a = λ r → asks≤-monitor n _ (k r) (a r)
  asks≤-monitor n       acc (coin _ k) a = λ b → asks≤-monitor n acc (k b) (a b)

-- `d` with an audit after every answer: the invariant is queried at exactly
-- the activation boundaries the trajectory observable inspects.
audited : Strat Query Answer → Strat Query Answer
audited (out b)    = out b
audited (ask q k)  = ask q λ a → ask audit λ _ → audited (k a)
audited (coin μ k) = coin μ λ b → audited (k b)

-- …and what that instrumentation costs an allowance: one extra ask per answer,
-- so the ask-depth doubles.  An asymptotic consumer charges it
-- (`UC.Asymptotic.saturatedHitᴺ-from-monitor`).
asks≤-audited : (n : ℕ) (d : Strat Query Answer) → asks≤ n d → asks≤ (n +ᴺ n) (audited d)
asks≤-audited _       (out _)    _ = tt
asks≤-audited (suc n) (ask _ k)  a = λ r →
  subst (λ m → asks≤ m (ask audit λ _ → audited (k r))) (sym (ℕP.+-suc n n))
        λ _ → asks≤-audited n (k r) (a r)
asks≤-audited n       (coin _ k) a = λ b → asks≤-audited n (k b) (a b)

module _ (vr : Variant) (s₀ : LState) where

  POVaudit : (ℕ → ℚ) → Set
  POVaudit = Bounded (Sys vr s₀) (watch s₀)

  -- The same statement at the DESIGNATED monitor, which is the one the UC
  -- layer's audit event is about (`UC.Seam.Audit.watched`): no strategy of
  -- budget `q` makes the monitor report a violation with probability above
  -- `ε q`.  `Trajectory.monitor-bounded` proves it from `POV`, and
  -- `ChimericLedger.Audit` hands it to the seam.
  POVmonitor : (ℕ → ℚ) → Set
  POVmonitor = Bounded (Sys vr s₀) (monitor s₀)

  -- The link to `POV`, STATED and not proved (`docs/protocol-rewrite.md` has
  -- the persistence argument and the price): a trajectory violation is seen by
  -- the audit form of the audit-interleaved strategy.
  TrajectoryFromAudit : Set
  TrajectoryFromAudit = (d : Strat Query Answer)
                      → PrHit (Sys vr s₀) (badTotal s₀) d ≤ℚ Pr (Sys vr s₀) (watch s₀ (audited d))

  -- …and how it is consumed, which IS proved.
  pov-via-audit : TrajectoryFromAudit → {ε : ℕ → ℚ} → POVaudit ε
                → (q qa : ℕ) (d : Strat Query Answer) → asks≤ q d → asks≤ qa (audited d)
                → PrHit (Sys vr s₀) (badTotal s₀) d ≤ℚ ε qa
  pov-via-audit tfa pa q qa d _ aa = ≤-trans (tfa d) (pa qa (audited d) aa)

-- An emulation at advantage `δ` carries an audit-form bound across:
-- `POVaudit` is `Bounded` on the nose, so this is `transfer`.
pov-transfer : (v₁ v₂ : Variant) (s₀ : LState) {ε δ : ℕ → ℚ}
             → Sys v₁ s₀ ≈adv[ δ ] Sys v₂ s₀
             → POVaudit v₁ s₀ ε → POVaudit v₂ s₀ (λ q → ε q +ℚ δ q)
pov-transfer v₁ v₂ s₀ {ε} {δ} =
  transfer {P = Sys v₁ s₀} {Sys v₂ s₀} {watch s₀} {ε} {δ} (asks≤-watch s₀)

------------------------------------------------------------------------
-- The birthday target
------------------------------------------------------------------------

-- The headline statement is pinned at a GENESIS state: all the value in ONE
-- UTxO output, keyed by a genesis hash `h₀`.  An account-only genesis (empty
-- UTxO set, all value in one account) is what the branch first stated, and it
-- is VACUOUS — `consumes inputConsuming` demands an input while `checkIns`
-- rejects every input against an empty UTxO set, so no transaction is ever
-- accepted, the oracle is never queried, the state never moves and the bad
-- event has probability zero (external theory review, finding 1).
-- `ChimericLedger.Pin` pins the liveness of the state below by `refl`, so the
-- vacuity cannot come back unnoticed.
genesis : Hash → Addr → ℕ → LState
genesis h₀ a V = ((h₀ , 0) , (a , V)) ∷ [] , []

-- The transaction that spends the genesis output, paying the value straight
-- back to the same address: the witness that the experiment runs.
spendGenesis : Hash → Addr → ℕ → Tx
spendGenesis h₀ a V = ((h₀ , 0) ∷ []) , [] , ((a , V) ∷ [])

accepted : Answer → Bool
accepted (ok b)      = b
accepted (totalIs _) = false

-- `ser`'s injectivity sits here because only the birthday bound consumes it (a
-- hash collision must come from two different transactions).
module AtBirthday (h₀ : Hash) (ser-inj : {t u : Tx} → ser t ≡ ser u → t ≡ u) where

  -- `q²` fresh-hash pairs, plus `q` chances for a fresh hash to hit `h₀`
  -- itself: the genesis key is in the namespace the oracle samples from, and
  -- an output keyed by an already-present key is swallowed by `unionNew`.
  εbirthday : ℕ → ℚ
  εbirthday q = fromℕ (q *ᴺ q +ᴺ q) * inv-pow-2 ℓ

  Target : Addr → ℕ → Set
  Target a V = POV inputConsuming (genesis h₀ a V) εbirthday
