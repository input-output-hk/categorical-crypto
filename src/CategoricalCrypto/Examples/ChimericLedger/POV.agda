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
-- lemma applies to.

open import Class.DecEq using (DecEq-List; DecEq-Bool)

open import Data.Bool.Base using (Bool; true; false; not; if_then_else_)
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_*_ to _*ᴺ_; _≡ᵇ_ to _≡ᴺ_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; _*_) renaming (_+_ to _+ℚ_; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-trans)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ProbabilisticLogic.Prelude using (fromℕ; inv-pow-2)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Examples.RandomOracle using (module RandomOracle)
open import CategoricalCrypto.Iface
open import CategoricalCrypto.OracleCall using (mapCall; reCall)
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
    go tbl (i , q) = found (RO.lookup-bs tbl q)
      where
        found : Maybe RO.Out → Calls unitᴵ (RO.Table × RO.Output)
        found (just h) = ret (tbl , (i , h))
        found nothing  = uniformVec ℓ λ h → ret ((q , h) ∷ tbl , (i , h))

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

Sys : Variant → LState → Protocol unitᴵ LedgerIf
Sys vr s₀ = ledger vr s₀ ∘ᵖ oracle

------------------------------------------------------------------------
-- The statement
------------------------------------------------------------------------

-- The system's state is the two components' — the ledger's is a projection.
ledgerOf : LState × RO.Table → LState
ledgerOf = proj₁

badTotal : LState → LState × RO.Table → Bool
badTotal s₀ st = not (total (ledgerOf st) ≡ᴺ total s₀)

-- THE STATEMENT: the bad event is a reached state, not an answer the ledger
-- gave about itself.
POV : Variant → LState → (ℕ → ℚ) → Set
POV vr s₀ = BoundedHit (Sys vr s₀) (badTotal s₀)

------------------------------------------------------------------------
-- The audit-form gadget
------------------------------------------------------------------------

-- Reading the ledger's own answers is not the statement, but it is the form
-- the transfer lemma applies to.  `watch` depends only on the audited
-- invariant, so both variants are watched by the same transformation.
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

-- `d` with an audit after every answer: the invariant is queried at exactly
-- the activation boundaries the trajectory observable inspects.
audited : Strat Query Answer → Strat Query Answer
audited (out b)    = out b
audited (ask q k)  = ask q λ a → ask audit λ _ → audited (k a)
audited (coin μ k) = coin μ λ b → audited (k b)

module _ (vr : Variant) (s₀ : LState) where

  POVaudit : (ℕ → ℚ) → Set
  POVaudit = Bounded (Sys vr s₀) (watch s₀)

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

-- The headline statement is pinned at a GENESIS state — empty UTxO set, all
-- value in one account — because a fresh hash can collide with a pre-existing
-- UTxO key, so a nonempty initial set would add a `q · |s₀|` term to the
-- bound.  `ser`'s injectivity sits here because only the birthday bound
-- consumes it (a hash collision must come from two different transactions).
module AtBirthday (ser-inj : {t u : Tx} → ser t ≡ ser u → t ≡ u) where

  εbirthday : ℕ → ℚ
  εbirthday q = fromℕ (q *ᴺ q) * inv-pow-2 ℓ

  genesis : Addr → ℕ → LState
  genesis a V = [] , (a , V) ∷ []

  Target : Addr → ℕ → Set
  Target a V = POV inputConsuming (genesis a V) εbirthday
