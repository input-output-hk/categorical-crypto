{-# OPTIONS --safe --without-K #-}

-- The birthday bound, proved: at the input-consuming variant, no strategy of
-- query budget `q` moves `total` away from genesis except with probability
-- `εbirthday q`.  `Protocol.Safety.hit-bounded` carries the adaptivity, so
-- what is owed here is a non-adaptive per-step certificate.
--
-- The certificate decomposes the statement into three independent pieces:
--
--   ledger rules + a fresh hash → conservation of `total`
--     — `Value.conservation`, with no probability in it;
--   oracle sampling → freshness fails with probability ≤ `εbirthday`
--     — the potential `φ`, over `Uniform.Duplicate.Φ`;
--   audit soundness → the observable bound
--     — `Observable.auditWatch-bounded`, downstream in `Property`.
--
-- Freshness fails in two quite different ways, and the invariant's `Stale`
-- field is what keeps them apart: a table HIT is a repeated query, excluded
-- outright by `no-replay`, while a coincidence of DISTINCT digests is the bad
-- event `φ` pays for.  The `Stale` witness for a freshly hashed transaction is
-- its FIRST INPUT, which exists only because `inputConsuming` demands one:
-- this is where the slides' repair is actually spent, and with `chimeric` in
-- its place `Stale` is false.

open import Class.DecEq

open import Data.Bool.Base using (Bool; true; false; not; _∨_)
open import Data.Bool.Properties using (T-≡; ∨-zeroʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; suc) renaming (_+_ to _+ᴺ_; _*_ to _*ᴺ_)
open import Data.Nat.Properties using (≡⇒≡ᵇ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Rational using (ℚ; 1ℚ; _*_) renaming (_≤_ to _≤ℚ_)
open import Data.Rational.Properties using (+-identityˡ; ≤-reflexive; ≤-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Function.Base using (case_of_)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Negation.Core using (¬_)

open import ProbabilisticLogic.Prelude
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.OracleCall
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Protocol.Safety

module CategoricalCrypto.Examples.ChimericLedger.Birthday
  (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) where

open Ledger ℓ
open Step ser

open import CategoricalCrypto.Examples.ChimericLedger.Observable ℓ ser
open import CategoricalCrypto.Examples.ChimericLedger.System ℓ ser
open import CategoricalCrypto.Examples.ChimericLedger.Value ℓ
open import ProbabilisticLogic.Distribution.Uniform.Birthday ℓ
-- `Hash` would clash with `Ledger.Hash`.
open import ProbabilisticLogic.Distribution.Uniform.Duplicate ℓ using
  (dup; memb; memb-∉; Φ; 0≤Φ; dup⇒1≤Φ; Φ-keep; Φ-fresh)

module _ (h₀ : Hash) (ser-inj : {t u : Tx} → ser t ≡ ser u → t ≡ u) where

  -- `q²` fresh-hash pairs, plus `q` chances for a fresh hash to hit `h₀`
  -- itself: the genesis key is in the namespace the oracle samples from, and
  -- an output keyed by an already-present key is swallowed by `unionNew`.
  εbirthday : ℕ → ℚ
  εbirthday q = fromℕ (q *ᴺ q +ᴺ q) * inv-pow-2 ℓ

  ----------------------------------------------------------------------
  -- The invariant
  ----------------------------------------------------------------------

  -- The four ways two hashings can interact, and what decides each:
  --   the same transaction resubmitted — a table HIT, not a collision between
  --     distinct inputs; excluded by `Stale` (this is `inputConsuming`'s job);
  --   distinct transactions with equal serialization — excluded by `ser-inj`,
  --     spent once, in `stale-not-accepted`;
  --   distinct queries with equal digests — the bad event, `flag`;
  --   a new output key `(h , i)` colliding with a live one — also `flag`,
  --     since `Good.hashed` keeps every live key's hash inside `Hs`.

  private
    -- The hashes in play, `h₀` among them: the genesis outputs are keyed by
    -- it, so a fresh digest may swallow them too.  That slot is the `+ q`.
    Hs : RO.Table → List Hash
    Hs []             = h₀ ∷ []
    Hs ((_ , h) ∷ tb) = h ∷ Hs tb

    flag : RO.Table → Bool
    flag tbl = dup (Hs tbl)

    -- A hash already in the table belongs to a transaction one of whose
    -- inputs is already spent — so it cannot be accepted again.
    record Stale (u : Utxo) (hs : List Hash) (qs : List Bool) : Set where
      constructor stale
      field
        tx    : Tx
        serEq : ser tx ≡ qs
        key   : TxIn
        key∈  : key ∈ proj₁ tx
        spent : lookupU u key ≡ nothing
        hash∈ : proj₁ key ∈ hs

    -- Same-transaction replay, excluded: `ser-inj` identifies the stale
    -- transaction with the submitted one, and `checkIns-live` insists every
    -- input the submitted one spends is still live.
    stale-not-accepted : ∀ u tx u′ vIn hs → checkIns u (proj₁ tx) ≡ just (vIn , u′)
                       → Stale u hs (ser tx) → ⊥
    stale-not-accepted u tx u′ vIn hs e₁ (stale t serEq k k∈ spent _) =
      checkIns-live u (proj₁ tx) vIn u′ k e₁
        (subst (λ z → k ∈ proj₁ z) (ser-inj serEq) k∈) spent

  module _ (a₀ : Addr) (V : ℕ) where

    private
      s₀ : LState
      s₀ = genesis h₀ a₀ V

      Sys₀ : Protocol unitᴵ LedgerIf
      Sys₀ = Sys inputConsuming s₀

      Bad : St Sys₀ → Bool
      Bad = badTotal s₀

      record Good (st : St Sys₀) : Set where
        field
          nodup  : flag (proj₂ st) ≡ false
          uniq   : Uniq (proj₁ (proj₁ st))
          hashed : ∀ k → k ∈ keysU (proj₁ (proj₁ st)) → proj₁ k ∈ Hs (proj₂ st)
          stales : All (λ e → Stale (proj₁ (proj₁ st)) (Hs (proj₂ st)) (proj₁ e)) (proj₂ st)
          intact : total (proj₁ st) ≡ total s₀

      Inv : St Sys₀ → Set
      Inv st = flag (proj₂ st) ≡ true ⊎ Good st

      φ : ℕ → St Sys₀ → ℚ
      φ m st = Φ m (Hs (proj₂ st))

    ----------------------------------------------------------------------
    -- Reading one activation
    ----------------------------------------------------------------------

    private
      newU : Utxo → List TxOut → Hash → Utxo
      newU u′ outs h = unionNew u′ (outsAt h 0 outs)

      step-rejected : ∀ s tbl tx → applyTx inputConsuming s tx ≡ pureᶜ (s , false)
                    → step Sys₀ (s , tbl) (submit tx) ≡ ret ((s , tbl) , ok false)
      step-rejected s tbl tx eq rewrite eq = refl

      step-accepted : ∀ s tbl ins wds outs {u′ a′}
        → applyTx inputConsuming s (ins , wds , outs)
          ≡ callᶜ (ser (ins , wds , outs)) (λ h → (newU u′ outs h , a′) , true)
        → step Sys₀ (s , tbl) (submit (ins , wds , outs))
          ≡ serve (ledger inputConsuming s₀) oracle
              (λ r → ret ((newU u′ outs (proj₂ r) , a′) , ok true))
              (step oracle tbl (fzero , ser (ins , wds , outs)))
      step-accepted s tbl ins wds outs eq rewrite eq = refl

      oracle-hit : ∀ tbl q h → RO.lookup-bs tbl q ≡ just h
                 → step oracle tbl (fzero , q) ≡ ret (tbl , (fzero , h))
      oracle-hit tbl q h eq rewrite eq = refl

      oracle-miss : ∀ tbl q → RO.lookup-bs tbl q ≡ nothing
                  → step oracle tbl (fzero , q)
                    ≡ uniformVec ℓ (λ h → ret ((q , h) ∷ tbl , (fzero , h)))
      oracle-miss tbl q eq rewrite eq = refl

      -- A table hit names a table entry, which `Stales` then indicts.
      lookup-bs-∈ : ∀ tbl q h → RO.lookup-bs tbl q ≡ just h
                  → Σ[ e ∈ List Bool × Hash ] ((e ∈ tbl) × (proj₁ e ≡ q))
      lookup-bs-∈ ((k , v) ∷ xs) q h eq with q ≟ k
      ... | yes p = (k , v) , here refl , sym p
      ... | no  _ with lookup-bs-∈ xs q h eq
      ...   | e , mem , pe = e , there mem , pe

    -- A hit at a good state is the replay, and it cannot happen: the table
    -- entry it names is indicted by `Stales`.
    private
      no-replay : ∀ s tbl tx u′ vIn h → checkIns (proj₁ s) (proj₁ tx) ≡ just (vIn , u′)
                → RO.lookup-bs tbl (ser tx) ≡ just h → Good (s , tbl) → ⊥
      no-replay s tbl tx u′ vIn h e₁ eo good with lookup-bs-∈ tbl (ser tx) h eo
      ... | e , mem , pe = stale-not-accepted (proj₁ s) tx u′ vIn (Hs tbl) e₁
              (subst (Stale (proj₁ s) (Hs tbl)) pe (All.lookup (Good.stales good) mem))

    ----------------------------------------------------------------------
    -- The invariant survives a freshly hashed transaction
    ----------------------------------------------------------------------

    private
      freshInv : ∀ s tbl ins wds outs u′ a′ vIn
               → checkIns (proj₁ s) ins ≡ just (vIn , u′)
               → consumes inputConsuming ins ≡ true
               → applyTx inputConsuming s (ins , wds , outs)
                 ≡ callᶜ (ser (ins , wds , outs)) (λ h → (newU u′ outs h , a′) , true)
               → Inv (s , tbl) → (h : Hash)
               → Inv ((newU u′ outs h , a′) , (ser (ins , wds , outs) , h) ∷ tbl)
      freshInv s tbl ins wds outs u′ a′ vIn e₁ ec eq (inj₁ fl) h =
        inj₁ (trans (cong (memb h (Hs tbl) ∨_) fl) (∨-zeroʳ (memb h (Hs tbl))))
      -- The empty-input case is refuted by `ec`: `consumes inputConsuming []`
      -- is `false`.  THIS is where the repair is spent — it is what puts a
      -- first input `i₀` in scope to be `headStale`'s `Stale.key`.
      freshInv s tbl (i₀ ∷ is) wds outs u′ a′ vIn e₁ ec eq (inj₂ good) h
        with memb h (Hs tbl) in em
      ... | true  = inj₁ refl
      ... | false = inj₂ record
            { nodup  = trans (cong (_∨ dup (Hs tbl)) em) (Good.nodup good)
            ; uniq   = uniq-unionNew u′ (outsAt h 0 outs) uniq′
            ; hashed = hashed′
            ; stales = headStale All.∷ tailStales tbl (Good.stales good)
            ; intact = trans
                (subst (λ c → total (proj₁ (runCall (λ _ → h) c)) ≡ total s) eq
                  (conservation ser inputConsuming s (i₀ ∷ is , wds , outs) (Hs tbl) h
                    (Good.hashed good) h∉))
                (Good.intact good)
            }
        where
        ins = i₀ ∷ is

        h∉ : ¬ (h ∈ Hs tbl)
        h∉ = memb-∉ (Hs tbl) h em

        uniq′ : Uniq u′
        uniq′ = checkIns-uniq (proj₁ s) ins vIn u′ (Good.uniq good) e₁

        -- Every hash the state knows about is one the fresh sample missed.
        known-≢ : ∀ k → proj₁ k ∈ Hs tbl → proj₁ k ≢ h
        known-≢ k mem p = h∉ (subst (_∈ Hs tbl) p mem)

        hashed′ : ∀ k → k ∈ keysU (newU u′ outs h) → proj₁ k ∈ h ∷ Hs tbl
        hashed′ k mem with keysU-unionNew-outsAt u′ h 0 outs k mem
        ... | inj₁ m′ = there (Good.hashed good k (checkIns-keysU (proj₁ s) ins vIn u′ k e₁ m′))
        ... | inj₂ p  = here p

        i₀∈ : proj₁ i₀ ∈ Hs tbl
        i₀∈ with checkIns-head (proj₁ s) i₀ is vIn u′ e₁
        ... | o , eqo = Good.hashed good i₀ (lookupU-just-∈ (proj₁ s) i₀ o eqo)

        headStale : Stale (newU u′ outs h) (h ∷ Hs tbl) (ser (ins , wds , outs))
        headStale = stale (ins , wds , outs) refl i₀ (here refl)
          (lookupU-unionNew-outsAt u′ h 0 outs i₀ (known-≢ i₀ i₀∈)
            (checkIns-consumed (proj₁ s) i₀ is vIn u′ (Good.uniq good) e₁))
          (there i₀∈)

        tailStale : {e : List Bool × Hash}
                  → Stale (proj₁ s) (Hs tbl) (proj₁ e)
                  → Stale (newU u′ outs h) (h ∷ Hs tbl) (proj₁ e)
        tailStale (stale t serEq k k∈ spent hash∈) = stale t serEq k k∈
          (lookupU-unionNew-outsAt u′ h 0 outs k (known-≢ k hash∈)
            (checkIns-lookupU (proj₁ s) ins vIn u′ k e₁ spent))
          (there hash∈)

        tailStales : (t : RO.Table)
                   → All (λ e → Stale (proj₁ s) (Hs tbl) (proj₁ e)) t
                   → All (λ e → Stale (newU u′ outs h) (h ∷ Hs tbl) (proj₁ e)) t
        tailStales []      All.[]       = All.[]
        tailStales (e ∷ t) (p All.∷ ps) = tailStale {e} p All.∷ tailStales t ps

    ----------------------------------------------------------------------
    -- The certificate
    ----------------------------------------------------------------------

    private
      -- Every activation that does not sample keeps the table, so it pays
      -- nothing and gains a unit of budget.
      point-step : (m : ℕ) (s : LState) (tbl : RO.Table) (s′ : LState) (ans : Answer)
                 → E⊥ (return⊥ ((s′ , tbl) , ans)) (λ sr → φ m (proj₁ sr)) ≤ℚ φ (suc m) (s , tbl)
      point-step m s tbl s′ ans = ≤-trans
        (≤-reflexive (E⊥-return ((s′ , tbl) , ans) (λ sr → φ m (proj₁ sr))))
        (Φ-keep m (Hs tbl))

      presTree : ∀ st q → Inv st → AllLeaves (λ sr → Inv (proj₁ sr)) (step Sys₀ st q)
      presTree (s , tbl) audit       inv = inv
      presTree (s , tbl) (submit tx) inv with shape ser inputConsuming s tx
      ... | rejected eq = subst (AllLeaves (λ sr → Inv (proj₁ sr)))
                                (sym (step-rejected s tbl tx eq)) inv
      presTree (s , tbl) (submit (ins , wds , outs)) inv
          | accepted vIn u′ a′ e₁ e₂ ec eq =
            subst (AllLeaves (λ sr → Inv (proj₁ sr)))
                  (sym (step-accepted s tbl ins wds outs eq)) served
        where
        qs = ser (ins , wds , outs)

        K : RO.Output → Calls HashIf (LState × Answer)
        K r = ret ((newU u′ outs (proj₂ r) , a′) , ok true)

        Goal : Set
        Goal = AllLeaves (λ sr → Inv (proj₁ sr))
                 (serve (ledger inputConsuming s₀) oracle K (step oracle tbl (fzero , qs)))

        hit : (h : Hash) → RO.lookup-bs tbl qs ≡ just h → Inv (s , tbl)
            → Inv ((newU u′ outs h , a′) , tbl)
        hit h eo (inj₁ fl)   = inj₁ fl
        hit h eo (inj₂ good) =
          ⊥-elim (no-replay s tbl (ins , wds , outs) u′ vIn h e₁ eo good)

        go : (r : Maybe Hash) → RO.lookup-bs tbl qs ≡ r → Goal
        go (just h) eo rewrite oracle-hit tbl qs h eo = hit h eo inv
        go nothing  eo rewrite oracle-miss tbl qs eo =
          AllLeaves-serve-uniformVec (ledger inputConsuming s₀) oracle K ℓ
            (λ h → ret ((qs , h) ∷ tbl , (fzero , h)))
            (freshInv s tbl ins wds outs u′ a′ vIn e₁ ec eq inv)

        served : Goal
        served = go (RO.lookup-bs tbl qs) refl

    private
      cert : HitCert Sys₀ Bad εbirthday
      cert = record
        { Inv    = Inv
        ; φ      = φ
        ; inv₀   = inj₂ record
            { nodup  = refl
            ; uniq   = refl , tt
            ; hashed = λ where k (here p) → here (cong proj₁ p)
            ; stales = All.[]
            ; intact = refl
            }
        ; pres   = λ st q inv → evalC-support (step Sys₀ st q) (presTree st q inv)
        ; φ-nn   = λ m st _ → 0≤Φ m (Hs (proj₂ st))
        ; φ-bad  = φ-bad
        ; φ-step = φ-step
        ; φ-init = λ m → ≤-trans (≤-reflexive (+-identityˡ (Γ 1 m))) (birthday m)
        }
        where
        φ-bad : ∀ m st → Inv st → Bad st ≡ true → 1ℚ ≤ℚ φ m st
        φ-bad m st (inj₁ fl)   _  = dup⇒1≤Φ m (Hs (proj₂ st)) fl
        φ-bad m st (inj₂ good) bd = case trans (sym bd)
          (cong not (Equivalence.to T-≡
            (≡⇒≡ᵇ (total (proj₁ st)) (total s₀) (Good.intact good)))) of λ ()

        φ-step : ∀ m st q → Inv st
               → E⊥ (kernel Sys₀ st q) (λ sr → φ m (proj₁ sr)) ≤ℚ φ (suc m) st
        φ-step m (s , tbl) audit _ = point-step m s tbl s (totalIs (total s))
        φ-step m (s , tbl) (submit tx) inv with shape ser inputConsuming s tx
        ... | rejected eq = subst (λ t → E⊥ (evalC t) (λ sr → φ m (proj₁ sr)) ≤ℚ φ (suc m) (s , tbl))
                                  (sym (step-rejected s tbl tx eq))
                                  (point-step m s tbl s (ok false))
        φ-step m (s , tbl) (submit (ins , wds , outs)) inv
            | accepted vIn u′ a′ e₁ e₂ ec eq =
              subst (λ t → E⊥ (evalC t) (λ sr → φ m (proj₁ sr)) ≤ℚ φ (suc m) (s , tbl))
                    (sym (step-accepted s tbl ins wds outs eq)) served
          where
          qs = ser (ins , wds , outs)

          K : RO.Output → Calls HashIf (LState × Answer)
          K r = ret ((newU u′ outs (proj₂ r) , a′) , ok true)

          F : St Sys₀ × Answer → ℚ
          F sr = φ m (proj₁ sr)

          -- The fresh sample detaches as ONE uniform draw over `Hs`'s head.
          expand : E⊥ (evalC (serve (ledger inputConsuming s₀) oracle K
                                (uniformVec ℓ (λ h → ret ((qs , h) ∷ tbl , (fzero , h))))))
                      F
                 ≡ E (uniform-Vec ℓ) (λ v → Φ m (v ∷ Hs tbl))
          expand = trans
            (evalC-serve-uniformVec (ledger inputConsuming s₀) oracle K ℓ
              (λ h → ret ((qs , h) ∷ tbl , (fzero , h))) (maybeℚ F))
            (trans (E-bind (uniform-Vec ℓ)
                     (λ v → evalC (serve (ledger inputConsuming s₀) oracle K
                              (ret ((qs , v) ∷ tbl , (fzero , v))))) (maybeℚ F))
                   (lookupᴰℚ-cong-P (entries (uniform-Vec ℓ))
                     (λ v → lookupᴰℚ-return
                              (just (((newU u′ outs v , a′) , (qs , v) ∷ tbl) , ok true))
                              (maybeℚ F))))

          fresh-bound : E⊥ (evalC (serve (ledger inputConsuming s₀) oracle K
                              (uniformVec ℓ (λ h → ret ((qs , h) ∷ tbl , (fzero , h)))))) F
                      ≤ℚ φ (suc m) (s , tbl)
          fresh-bound = ≤-trans (≤-reflexive expand) (Φ-fresh m (Hs tbl))

          StepGoal : Set
          StepGoal = E⊥ (evalC (serve (ledger inputConsuming s₀) oracle K
                                  (step oracle tbl (fzero , qs)))) F
                   ≤ℚ φ (suc m) (s , tbl)

          go : (r : Maybe Hash) → RO.lookup-bs tbl qs ≡ r → StepGoal
          go (just h) eo rewrite oracle-hit tbl qs h eo =
            point-step m s tbl (newU u′ outs h , a′) (ok true)
          go nothing  eo rewrite oracle-miss tbl qs eo = fresh-bound

          served : StepGoal
          served = go (RO.lookup-bs tbl qs) refl

    target : TrajectoryLossBounded inputConsuming (genesis h₀ a₀ V) εbirthday
    target = hit-bounded Sys₀ Bad cert
