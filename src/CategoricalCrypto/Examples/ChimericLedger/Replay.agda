{-# OPTIONS --safe --without-K #-}

-- The chimeric variant destroys value at every hash width and serialization.
-- No hash collision is needed: a transaction with no inputs is resubmitted
-- verbatim, the oracle answers the repeat from its table
-- (`System.oracle-repeat`), and `unionNew` keeps the first output while the
-- withdrawal is charged twice.  `inputConsuming` rejects the transaction.
-- The attack runs from a funded account, unreachable from `System.genesis`
-- (see `Transfer.Chimericᶠ`); `Genesis` pins instead that the positive theorem's own
-- initialization is live.  Walkthrough: `docs/end-to-end.md` §2.

open import Class.DecEq
open import Class.DecEq.Ext

open import Data.Bool.Base
open import Data.Bool.Properties
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base
open import Data.Nat.Base renaming (_≡ᵇ_ to _≡ᴺ_)
open import Data.Nat.Properties
open import Data.Nat.Properties.Ext
open import Data.Product.Base
open import Data.Rational using (0ℚ; 1ℚ)
open import Data.Unit.Base
open import Data.Vec.Base
open import Function.Bundles
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.OracleCall
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

import CategoricalCrypto.Examples.ChimericLedger.Observable as Observable
import CategoricalCrypto.Examples.ChimericLedger.System     as System

module CategoricalCrypto.Examples.ChimericLedger.Replay where

-- See `ChimericLedger`; here `≟-refl` must also resolve at the instance
-- `lookupU` was elaborated against.
private instance DecEq-×′ = DecEq-×

------------------------------------------------------------------------
-- The attack
------------------------------------------------------------------------

module Attack (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) (V : ℕ) where

  open Ledger ℓ
  open Step ser
  open Observable ℓ ser
  open System ℓ ser

  s₀ : LState
  s₀ = [] , (0 , suc (suc V)) ∷ []

  txᵃ : Tx
  txᵃ = [] , ((0 , 1) ∷ []) , ((1 , 1) ∷ [])

  once twice : Hash → LState
  once  h = after chimeric s₀ txᵃ h
  twice h = after chimeric (once h) txᵃ h

  preserved : (h : Hash) → total (once h) ≡ total s₀
  preserved _ = refl

  twice-shape : (h : Hash) → twice h ≡ (((h , 0) , (1 , 1)) ∷ [] , (0 , V) ∷ [])
  twice-shape h rewrite ≟-refl {A = TxIn} (h , 0) = refl

  destroyed : (h : Hash) → total (twice h) ≡ suc (V + 0)
  destroyed h = cong total (twice-shape h)

  rejected : (h : Hash) → proj₂ (runCall (λ _ → h) (applyTx inputConsuming s₀ txᵃ)) ≡ false
  rejected _ = refl

  replay : Strat Query Answer
  replay = ask (submit txᵃ) λ _ → ask (submit txᵃ) λ _ → ask audit λ _ → out false

  replay-asks : asks≤ 3 replay
  replay-asks _ _ _ = tt

  -- `t` is the total the WATCH measures against, which need not be spelled
  -- as the start state's: the family property reads the watch at the UTxO
  -- genesis total while the attack runs at a funded account of the same total.
  module _ (t : ℕ) (tot : t ≡ total s₀) where

    private
      P : Protocol unitᴵ LedgerIf
      P = Sys chimeric s₀

      tbl : Hash → RO.Table
      tbl h = (ser txᵃ , h) ∷ []

      W₁ : Strat Query Answer
      W₁ = auditWatchFrom t false (ask (submit txᵃ) λ _ → ask audit λ _ → out false)

      K₁ : St P × Answer → Dist⊥ Bool
      K₁ st = runFrom P (proj₁ st) W₁

      μ₁ : Hash → Dist⊥ (St P × Answer)
      μ₁ h = return⊥ ((once h , tbl h) , ok true)

      first-shape : kernel P (s₀ , []) (submit txᵃ) ≈Mℚ (uniform-Vec ℓ >>=ᴹ μ₁)
      first-shape = evalC-serve-uniformVec (ledger chimeric s₀) oracle κ ℓ fresh
        where
        κ : RO.Output → Calls HashIf (LState × Answer)
        κ ih = ret (once (proj₂ ih) , ok true)

        fresh : Hash → Calls unitᴵ (RO.Table × RO.Output)
        fresh h = ret (tbl h , (fzero , h))

      second-shape : (h : Hash) → kernel P (once h , tbl h) (submit txᵃ)
                                  ≡ return⊥ ((twice h , tbl h) , ok true)
      second-shape h = cong (λ t → evalC (serve (ledger chimeric s₀) oracle κ t))
                            (oracle-repeat [] fzero (ser txᵃ) h)
        where
        κ : RO.Output → Calls HashIf (LState × Answer)
        κ ih = ret (after chimeric (once h) txᵃ (proj₂ ih) , ok true)

      branch : (h : Hash) → Pr₁⊥ (runFrom P (once h , tbl h) W₁) ≡ 1ℚ
      branch h = begin
        Pr₁⊥ (kernel P (once h , tbl h) (submit txᵃ) >>=⊥ G)
          ≡⟨ cong (λ μ → Pr₁⊥ (μ >>=⊥ G)) (second-shape h) ⟩
        Pr₁⊥ (return⊥ ((twice h , tbl h) , ok true) >>=⊥ G)
          ≡⟨ >>=⊥-identityˡ ((twice h , tbl h) , ok true) G mb ⟩
        Pr₁⊥ (kernel P (twice h , tbl h) audit >>=⊥ Gᵃ)
          ≡⟨ >>=⊥-identityˡ ((twice h , tbl h) , totalIs (total (twice h))) Gᵃ mb ⟩
        Pr₁⊥ (return⊥ (not (total (twice h) ≡ᴺ t)))
          ≡⟨ cong (λ b → Pr₁⊥ (return⊥ (not b))) miss ⟩
        Pr₁⊥ (return⊥ true)
          ≡⟨ lookupᴰℚ-return (just true) mb ⟩
        1ℚ ∎
        where
        open ≡-Reasoning

        G : St P × Answer → Dist⊥ Bool
        G st = runFrom P (proj₁ st) (ask audit λ a → out (lostValue t a))

        Gᵃ : St P × Answer → Dist⊥ Bool
        Gᵃ st = runFrom P (proj₁ st) (out (lostValue t (proj₂ st)))

        miss : (total (twice h) ≡ᴺ t) ≡ false
        miss = trans (cong₂ _≡ᴺ_ (destroyed h) tot) (n≡ᵇsuc (V + 0))

    chimeric-loses-value : Pr P (auditWatch t replay) ≡ 1ℚ
    chimeric-loses-value =
      Pr₁⊥-bind-const (kernel P (s₀ , []) (submit txᵃ)) (uniform-Vec ℓ) μ₁ K₁ 1ℚ first-shape hit
      where
      hit : (h : Hash) → Pr₁⊥ (μ₁ h >>=⊥ K₁) ≡ 1ℚ
      hit h = trans (>>=⊥-identityˡ ((once h , tbl h) , ok true) K₁ mb) (branch h)

------------------------------------------------------------------------
-- The genesis the positive theorem starts at is live
------------------------------------------------------------------------

-- `Pr` is 0 both when the ledger is safe and when it deadlocks, so the
-- genesis the birthday bound starts at is pinned live: its output is spent
-- with probability one, through the oracle (`docs/rewrite-verdict.md`,
-- Addendum, finding 1).  One accepted transaction is not global liveness.

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
  moved h = after inputConsuming g₀ txᵍ h

  private
    vtest : ((V + 0) + 0 ≡ᴺ V + 0) ≡ true
    vtest = Equivalence.to T-≡ (≡⇒≡ᵇ ((V + 0) + 0) (V + 0) (+-identityʳ (V + 0)))

    -- The key test is rewritten TWICE: `removeIn`'s copy sits behind
    -- `checkIns`'s `case` until the first is discharged.
    call-shape : applyTx inputConsuming g₀ txᵍ
               ≡ callᶜ (ser txᵍ) λ h → ((((h , 0) , (a , V)) ∷ [] , []) , true)
    call-shape rewrite ≟-refl {A = TxIn} (h₀ , 0) | ≟-refl {A = TxIn} (h₀ , 0) | vtest = refl

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
    step-shape = cong (λ c → graft L oracle (fromCall (submitCall c)) []) call-shape

    ν : Hash → Dist⊥ (St Pᵍ × Answer)
    ν h = evalC (serve L oracle κ (fresh h))

  genesis-live : Pr Pᵍ spend ≡ 1ℚ
  genesis-live =
    trans (cong (λ t → Pr₁⊥ (evalC t >>=⊥ K)) step-shape)
          (Pr₁⊥-bind-const (evalC (serve L oracle κ (uniformVec ℓ fresh))) (uniform-Vec ℓ) ν K 1ℚ
                           (evalC-serve-uniformVec L oracle κ ℓ fresh) hit)
    where
    K : St Pᵍ × Answer → Dist⊥ Bool
    K st = runFrom Pᵍ (proj₁ st) (out (accepted (proj₂ st)))

    hit : (h : Hash) → Pr₁⊥ (ν h >>=⊥ K) ≡ 1ℚ
    hit h = trans (>>=⊥-identityˡ (((((h , 0) , (a , V)) ∷ [] , []) , tblᵍ h) , ok true) K mb)
                  (lookupᴰℚ-return (just true) mb)

------------------------------------------------------------------------
-- The ℓ = 1 regression instance
------------------------------------------------------------------------

-- At 1-bit hashes and the constant serialization every statement holds by
-- `refl`, oracle sampling and ℚ arithmetic included.

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

chimeric-loses-value : Pr (Sys chimeric s₀) (auditWatch (total s₀) replay) ≡ 1ℚ
chimeric-loses-value = refl

consuming-preserves-value : Pr (Sys inputConsuming s₀) (auditWatch (total s₀) replay) ≡ 0ℚ
consuming-preserves-value = refl

h₁ : Hash
h₁ = replicate 1 true

module OneG = Genesis 1 (λ _ → []) h 0 2
open OneG using (g₀; spend)

genesis-live : Pr (Sys inputConsuming g₀) spend ≡ 1ℚ
genesis-live = refl

genesis-moves : after inputConsuming g₀ (spendGenesis h 0 2) h₁
              ≡ (((h₁ , 0) , (0 , 2)) ∷ [] , [])
genesis-moves = refl

genesis-preserves : PrHit (Sys inputConsuming g₀) (badTotal g₀) spend ≡ 0ℚ
genesis-preserves = refl
