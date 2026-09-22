{-# OPTIONS --safe --without-K #-}

-- The chimeric variant destroys value, at EVERY hash width and EVERY
-- serialization.
--
-- No hash collision is needed, only the determinism of `hash tx`: a
-- transaction with no inputs can be resubmitted verbatim, the oracle answers
-- the second query from its table (`System.oracle-repeat`), the replayed
-- output's key is the one the first submission created, and since `unionNew`
-- keeps the entry already present the withdrawal is charged twice while only
-- one output exists.  `inputConsuming` rejects the transaction outright, so
-- there is nothing to replay — the one place the slides' repair is spent.
-- Because the SAME transaction is submitted twice, the argument never needs
-- two transactions to share an encoding: it is compatible with `SerInj`.
--
-- What does NOT generalize is the initialization.  The attack needs a funded
-- ACCOUNT and nothing credits one (`System.ledger-keeps-accts-[]`), so no
-- prefix reaches it from the UTxO genesis the positive theorem is stated at;
-- `ChimericLedger.ReplayFamily` draws the asymptotic consequence and states
-- that gap.  `Genesis` instead pins what the positive theorem's own
-- initialization does: it is live, and the spend moves the state.
--
-- The ℓ = 1 instance at the bottom keeps every statement a `refl`, oracle
-- sampling and ℚ arithmetic included.

open import Class.DecEq
open import Class.DecEq.Ext

open import Data.Bool.Base
open import Data.Bool.Properties using (T-≡)
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base renaming (_≡ᵇ_ to _≡ᴺ_)
open import Data.Nat.Properties using (+-identityʳ; ≡⇒≡ᵇ)
open import Data.Nat.Properties.Ext using (n≡ᵇsuc)
open import Data.Product.Base
open import Data.Rational using (0ℚ; 1ℚ)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (replicate)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Prelude
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E; E-bind; E-const)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.OracleCall
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

import CategoricalCrypto.Examples.ChimericLedger.Observable as Observable
import CategoricalCrypto.Examples.ChimericLedger.System     as System

module CategoricalCrypto.Examples.ChimericLedger.Replay where

-- As `ChimericLedger` does: `DecEq-×` is not an upstream instance, and the key
-- type `TxIn` needs it for `≟-refl` to resolve at the same instance `lookupU`
-- was elaborated against.
private instance DecEq-×′ = DecEq-×

------------------------------------------------------------------------
-- The attack
------------------------------------------------------------------------

module Attack (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) (V : ℕ) where

  open Ledger ℓ
  open Step ser
  open Observable ℓ ser
  open System ℓ ser

  -- `2 + V` units in one account, and a transaction with no inputs moving one
  -- of them out: `consumes chimeric` waves it through.
  s₀ : LState
  s₀ = [] , (0 , suc (suc V)) ∷ []

  txᵃ : Tx
  txᵃ = [] , ((0 , 1) ∷ []) , ((1 , 1) ∷ [])

  once twice : Hash → LState
  once  h = proj₁ (runCall (λ _ → h) (applyTx chimeric s₀ txᵃ))
  twice h = proj₁ (runCall (λ _ → h) (applyTx chimeric (once h) txᵃ))

  preserved : (h : Hash) → total (once h) ≡ total s₀
  preserved _ = refl

  twice-shape : (h : Hash) → twice h ≡ (((h , 0) , (1 , 1)) ∷ [] , (0 , V) ∷ [])
  twice-shape h rewrite ≟-refl {A = TxIn} (h , 0) = refl

  -- A unit of value is gone.
  destroyed : (h : Hash) → total (twice h) ≡ suc (V + 0)
  destroyed h = cong total (twice-shape h)

  rejected : (h : Hash) → proj₂ (runCall (λ _ → h) (applyTx inputConsuming s₀ txᵃ)) ≡ false
  rejected _ = refl

  -- Submit the same no-input transaction twice, then audit.
  replay : Strat Query Answer
  replay = ask (submit txᵃ) λ _ → ask (submit txᵃ) λ _ → ask audit λ _ → out false

  replay-asks : asks≤ 3 replay
  replay-asks _ _ _ = tt

  -- The watch buys no queries, so three is the whole certificate: there is no
  -- initialization prefix to charge on top of it (header).
  replay-watch-asks : (r : LState) → asks≤ 3 (auditWatch r replay)
  replay-watch-asks r = asks≤-auditWatch r 3 false replay replay-asks

  -- `r` is the state the WATCH measures against, which need not be the state
  -- the system starts in: the family property reads the watch at the UTxO
  -- genesis while the attack runs at a funded account of the same total.
  module _ (r : LState) (totr : total r ≡ total s₀) where

    private
      P : Protocol unitᴵ LedgerIf
      P = Sys chimeric s₀

      tbl : Hash → RO.Table
      tbl h = (ser txᵃ , h) ∷ []

      W₁ : Strat Query Answer
      W₁ = auditWatchFrom r false (ask (submit txᵃ) λ _ → ask audit λ _ → out false)

      K₁ : St P × Answer → Dist⊥ Bool
      K₁ st = runFrom P (proj₁ st) W₁

      μ₁ : Hash → Dist⊥ (St P × Answer)
      μ₁ h = return⊥ ((once h , tbl h) , ok true)

      -- The first submission is the only sampling in the run: its query is
      -- fresh, so the oracle draws `uniformVec ℓ` and the run splits.
      first-shape : kernel P (s₀ , []) (submit txᵃ) ≈Mℚ (uniform-Vec ℓ >>=ᴹ μ₁)
      first-shape = evalC-serve-uniformVec (ledger chimeric s₀) oracle κ ℓ fresh
        where
        κ : RO.Output → Calls HashIf (LState × Answer)
        κ ih = ret (once (proj₂ ih) , ok true)

        fresh : Hash → Calls unitᴵ (RO.Table × RO.Output)
        fresh h = ret (tbl h , (fzero , h))

      -- The second asks the SAME point, so it is answered from the table and
      -- nothing further is sampled.
      second-shape : (h : Hash) → kernel P (once h , tbl h) (submit txᵃ)
                                  ≡ return⊥ ((twice h , tbl h) , ok true)
      second-shape h = cong (λ t → evalC (serve (ledger chimeric s₀) oracle (κ h) t))
                            (oracle-repeat [] fzero (ser txᵃ) h)
        where
        κ : Hash → RO.Output → Calls HashIf (LState × Answer)
        κ h ih = ret (proj₁ (runCall (λ _ → proj₂ ih) (applyTx chimeric (once h) txᵃ)) , ok true)

      -- Every branch of the sample ends at the same audit answer, so the
      -- verdict does not depend on the hash at all.
      branch : (h : Hash) → Pr₁⊥ (runFrom P (once h , tbl h) W₁) ≡ 1ℚ
      branch h = begin
        Pr₁⊥ (kernel P (once h , tbl h) (submit txᵃ) >>=⊥ G)
          ≡⟨ cong (λ μ → Pr₁⊥ (μ >>=⊥ G)) (second-shape h) ⟩
        Pr₁⊥ (return⊥ ((twice h , tbl h) , ok true) >>=⊥ G)
          ≡⟨ >>=⊥-identityˡ ((twice h , tbl h) , ok true) G mb ⟩
        Pr₁⊥ (kernel P (twice h , tbl h) audit >>=⊥ Gᵃ)
          ≡⟨ >>=⊥-identityˡ ((twice h , tbl h) , totalIs (total (twice h))) Gᵃ mb ⟩
        Pr₁⊥ (return⊥ (not (total (twice h) ≡ᴺ total r)))
          ≡⟨ cong (λ b → Pr₁⊥ (return⊥ (not b))) miss ⟩
        Pr₁⊥ (return⊥ true)
          ≡⟨ lookupᴰℚ-return (just true) mb ⟩
        1ℚ ∎
        where
        open ≡-Reasoning

        G : St P × Answer → Dist⊥ Bool
        G st = runFrom P (proj₁ st) (ask audit λ a → out (lostValue r a))

        Gᵃ : St P × Answer → Dist⊥ Bool
        Gᵃ st = runFrom P (proj₁ st) (out (lostValue r (proj₂ st)))

        miss : (total (twice h) ≡ᴺ total r) ≡ false
        miss = trans (cong₂ _≡ᴺ_ (destroyed h) totr) (n≡ᵇsuc (V + 0))

    -- Loss with probability ONE, through the accumulated audit event the
    -- family property reads.
    chimeric-loses-value : Pr P (auditWatch r replay) ≡ 1ℚ
    chimeric-loses-value = begin
      Pr₁⊥ (kernel P (s₀ , []) (submit txᵃ) >>=⊥ K₁)
        ≡⟨ >>=⊥-congʳ K₁ (kernel P (s₀ , []) (submit txᵃ)) (uniform-Vec ℓ >>=ᴹ μ₁) first-shape mb ⟩
      Pr₁⊥ ((uniform-Vec ℓ >>=ᴹ μ₁) >>=⊥ K₁)
        ≡⟨ >>=ᴹ-assoc (uniform-Vec ℓ) μ₁ (kmaybe K₁) mb ⟩
      Pr₁⊥ (uniform-Vec ℓ >>=ᴹ λ h → μ₁ h >>=⊥ K₁)
        ≡⟨ E-bind (uniform-Vec ℓ) (λ h → μ₁ h >>=⊥ K₁) mb ⟩
      E (uniform-Vec ℓ) (λ h → Pr₁⊥ (μ₁ h >>=⊥ K₁))
        ≡⟨ lookupᴰℚ-cong-P (entries (uniform-Vec ℓ)) hit ⟩
      E (uniform-Vec ℓ) (λ _ → 1ℚ)
        ≡⟨ E-const (uniform-Vec ℓ) 1ℚ ⟩
      1ℚ ∎
      where
      open ≡-Reasoning

      hit : (h : Hash) → Pr₁⊥ (μ₁ h >>=⊥ K₁) ≡ 1ℚ
      hit h = trans (>>=⊥-identityˡ ((once h , tbl h) , ok true) K₁ mb) (branch h)

------------------------------------------------------------------------
-- The genesis the positive theorem starts at is live
------------------------------------------------------------------------

-- `Pr` is 0ℚ both when the ledger is safe and when it is dead-locked, which is
-- what let an account-only genesis pass as a birthday target (external theory
-- review, finding 1).  So the UTxO genesis is pinned live — its output IS
-- spendable, with probability one and through the oracle — and pinned to move.
-- One accepted transaction is not global liveness, and nothing below is a
-- premise of any safety theorem.

module Genesis (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) (h₀ : Ledger.Hash ℓ) (a V : ℕ) where

  open Ledger ℓ
  open Step ser
  open Observable ℓ ser
  open System ℓ ser

  g₀ : LState
  g₀ = genesis h₀ a V

  txᵍ : Tx
  txᵍ = spendGenesis h₀ a V

  spend : Strat Query Answer
  spend = ask (submit txᵍ) λ ans → out (accepted ans)

  moved : Hash → LState
  moved h = proj₁ (runCall (λ _ → h) (applyTx inputConsuming g₀ txᵍ))

  private
    -- The value test `(V + 0) + 0 ≡ᴺ V + 0` is the one piece of the spend's
    -- arithmetic that is not already a literal.
    vtest : ((V + 0) + 0 ≡ᴺ V + 0) ≡ true
    vtest = Equivalence.to T-≡ (≡⇒≡ᵇ ((V + 0) + 0) (V + 0) (+-identityʳ (V + 0)))

    -- `applyTx` is stuck at an abstract `h₀` and `V`, so the activation is read
    -- through the call it makes.  The key test goes TWICE: `removeIn`'s copy of
    -- it sits behind `checkIns`'s `case` until the first one is discharged.
    call-shape : applyTx inputConsuming g₀ txᵍ
               ≡ callᶜ (ser txᵍ) λ h → ((((h , 0) , (a , V)) ∷ [] , []) , true)
    call-shape rewrite ≟-refl {A = TxIn} (h₀ , 0) | ≟-refl {A = TxIn} (h₀ , 0) | vtest = refl

  -- The genesis output is consumed and its value reappears under the
  -- transaction's own hash.
  genesis-moves : (h : Hash) → moved h ≡ (((h , 0) , (a , V)) ∷ [] , [])
  genesis-moves h = cong (λ c → proj₁ (runCall (λ _ → h) c)) call-shape

  private
    Pᵍ : Protocol unitᴵ LedgerIf
    Pᵍ = Sys inputConsuming g₀

    L : Protocol HashIf LedgerIf
    L = ledger inputConsuming g₀

    tblᵍ : Hash → RO.Table
    tblᵍ h = (ser txᵍ , h) ∷ []

    κ : RO.Output → Calls HashIf (LState × Answer)
    κ ih = ret ((((proj₂ ih , 0) , (a , V)) ∷ [] , []) , ok true)

    fresh : Hash → Calls unitᴵ (RO.Table × RO.Output)
    fresh h = ret (tblᵍ h , (fzero , h))

    step-shape : step Pᵍ (g₀ , []) (submit txᵍ) ≡ serve L oracle κ (uniformVec ℓ fresh)
    step-shape = cong (λ c → graft L oracle (fromCall (reCall (fzero ,_) proj₂
                        (mapCall (λ sb → proj₁ sb , ok (proj₂ sb)) c))) [])
                      call-shape

    ν : Hash → Dist⊥ (St Pᵍ × Answer)
    ν h = evalC (serve L oracle κ (fresh h))

  genesis-live : Pr Pᵍ spend ≡ 1ℚ
  genesis-live = begin
    Pr₁⊥ (evalC (step Pᵍ (g₀ , []) (submit txᵍ)) >>=⊥ K)
      ≡⟨ cong (λ t → Pr₁⊥ (evalC t >>=⊥ K)) step-shape ⟩
    Pr₁⊥ (evalC (serve L oracle κ (uniformVec ℓ fresh)) >>=⊥ K)
      ≡⟨ >>=⊥-congʳ K (evalC (serve L oracle κ (uniformVec ℓ fresh)))
           (uniform-Vec ℓ >>=ᴹ ν) (evalC-serve-uniformVec L oracle κ ℓ fresh) mb ⟩
    Pr₁⊥ ((uniform-Vec ℓ >>=ᴹ ν) >>=⊥ K)
      ≡⟨ >>=ᴹ-assoc (uniform-Vec ℓ) ν (kmaybe K) mb ⟩
    Pr₁⊥ (uniform-Vec ℓ >>=ᴹ λ h → ν h >>=⊥ K)
      ≡⟨ E-bind (uniform-Vec ℓ) (λ h → ν h >>=⊥ K) mb ⟩
    E (uniform-Vec ℓ) (λ h → Pr₁⊥ (ν h >>=⊥ K))
      ≡⟨ lookupᴰℚ-cong-P (entries (uniform-Vec ℓ)) hit ⟩
    E (uniform-Vec ℓ) (λ _ → 1ℚ)
      ≡⟨ E-const (uniform-Vec ℓ) 1ℚ ⟩
    1ℚ ∎
    where
    open ≡-Reasoning

    K : St Pᵍ × Answer → Dist⊥ Bool
    K st = runFrom Pᵍ (proj₁ st) (out (accepted (proj₂ st)))

    hit : (h : Hash) → Pr₁⊥ (ν h >>=⊥ K) ≡ 1ℚ
    hit h = trans (>>=⊥-identityˡ (((((h , 0) , (a , V)) ∷ [] , []) , tblᵍ h) , ok true) K mb)
                  (lookupᴰℚ-return (just true) mb)

------------------------------------------------------------------------
-- The ℓ = 1 regression instance
------------------------------------------------------------------------

-- Everything above, computed: at 1-bit hashes and the constant serialization
-- each statement holds by `refl`, oracle sampling and ℚ arithmetic included.
-- The constant `ser` costs nothing here — the attack submits ONE transaction
-- twice, so it never needs two transactions to share an encoding.

open Ledger 1
open Step (λ _ → [])
open Observable 1 (λ _ → [])
open System 1 (λ _ → [])

module One = Attack 1 (λ _ → []) 0
open One using (s₀; txᵃ; once; twice; replay; replay-asks)

h : Hash
h = replicate 1 false

initial-total : total s₀ ≡ 2
initial-total = refl

preserved : total (once h) ≡ 2
preserved = refl

destroyed : total (twice h) ≡ 1
destroyed = refl

rejected : proj₂ (runCall (λ _ → h) (applyTx inputConsuming s₀ txᵃ)) ≡ false
rejected = refl

chimeric-loses-value : Pr (Sys chimeric s₀) (auditWatch s₀ replay) ≡ 1ℚ
chimeric-loses-value = refl

consuming-preserves-value : Pr (Sys inputConsuming s₀) (auditWatch s₀ replay) ≡ 0ℚ
consuming-preserves-value = refl

h₀ h₁ : Hash
h₀ = replicate 1 false
h₁ = replicate 1 true

module OneG = Genesis 1 (λ _ → []) h₀ 0 2
open OneG using (g₀; spend)

genesis-live : Pr (Sys inputConsuming g₀) spend ≡ 1ℚ
genesis-live = refl

genesis-moves : proj₁ (runCall (λ _ → h₁) (applyTx inputConsuming g₀ (spendGenesis h₀ 0 2)))
              ≡ (((h₁ , 0) , (0 , 2)) ∷ [] , [])
genesis-moves = refl

genesis-preserves : PrHit (Sys inputConsuming g₀) (badTotal g₀) spend ≡ 0ℚ
genesis-preserves = refl
