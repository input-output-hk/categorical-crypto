{-# OPTIONS --safe --without-K --guardedness #-}

-- Preservation of value, carried across a UC emulation — and the three public
-- claims of the example, kept apart.
--
--   `preserves-value-transfer`  OBSERVABLE AUDIT SAFETY.  Assumes `SerInj` and
--     an emulation; bounds the probability that a discrepant audit ANSWER is
--     accumulated during an interaction and reported when it terminates.  It
--     is not a statement about the implementation's internal state, and not a
--     statement that the implementation answers at all.
--
--   `ledger-uc-to-pov-family`  AUDIT TO TRAJECTORY.  The appendix.  Assumes
--     the above plus `TruthfulAudit`, and pays `withAudits`' doubled
--     allowance; it concludes about the real system's own state trajectory.
--
--   `ideal-spends-genesis`  POSITIVE BEHAVIOUR.  Assumes nothing.  At every
--     level the genesis output is spent with probability one and the state
--     moves.  One accepted transaction is not global liveness, and no safety
--     theorem above takes it as a premise.
--
-- `ledger-preserves-value-from-hash` is the slides' last step: the emulation
-- premise may be about the HASH alone, because the closed system factors
-- through a hash port.  `Mute` and `Liar` at the bottom pin what the first two
-- claims do NOT say.

open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Bool.Properties using (∨-identityʳ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
open import Data.Rational.Properties using (+-identityʳ)
open import Data.Rational.Properties.Ext using (0≤*; 1≰0)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; subst₂; sym; trans)
open import Relation.Nullary.Negation.Core using (¬_)

open import ProbabilisticLogic.Prelude
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E-bind; E-const)
open import ProbabilisticLogic.Distribution.Uniform using (0≤fromℕ; 0≤inv-pow-2)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Examples.ChimericLedger.QueryBound
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Asymptotic
open import CategoricalCrypto.UC.Asymptotic.Compose
open import CategoricalCrypto.UC.Asymptotic.Contextual
open import CategoricalCrypto.UC.Asymptotic.Family
open import CategoricalCrypto.UC.Budget
open import CategoricalCrypto.UC.Factor
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Family
open import CategoricalCrypto.UC.Model.Family.Ingest
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Saturated
open import CategoricalCrypto.UC.Seam.Grounded

import CategoricalCrypto.Examples.ChimericLedger.Replay as Replay

module CategoricalCrypto.Examples.ChimericLedger.Transfer
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

open import CategoricalCrypto.Examples.ChimericLedger.Property ser

------------------------------------------------------------------------
-- Claim 1: observable audit safety
------------------------------------------------------------------------

-- The point of the example: the proved ideal bound plus an emulation premise
-- give the SAME property about the real system, with nothing else assumed.
-- `R ≤UC^ωⁿ I` is an allowance-uniform emulation with negligible error.
preserves-value-transfer : (a V : ℕ) (R : Systems LedgerIf^ω) → SerInj
                         → R ≤UC^ωⁿ Ideal a V → PreservesValue a V R
preserves-value-transfer a V R si em =
  uc-preservesᴺ {R = R} {I = Ideal a V} {ε = εᴸ} {bad = auditWatch a V}
    (auditWatch-preserving a V) (≤UC^ωⁿ⇒≈negl {R = R} {I = Ideal a V} em)
    (ideal-preserves-value a V si)

------------------------------------------------------------------------
-- …off a premise about the hash alone
------------------------------------------------------------------------

-- The factoring `Sysᴴ hash = ledger ∘ᵖ hash` exists at the protocol layer
-- already, but everything the UC layer sees is the CLOSED system, inside
-- which the hash is invisible.  `ledger-factor` repairs that reading: the
-- same closed system is `ledgerᵒ ∙ hashᵒ hash` regraded by the unit, where
-- `hashPortᵒ` is the exposed port.  What it buys is `hash-liftⁿ`; what it
-- does NOT give is a nontrivial simulator (`docs/ledger-factoring.md`).

HashIf^ω : ℕ → Iface
HashIf^ω = AtLevel.HashIf

hashPortᵒ : ℕ → Channel
hashPortᵒ n = ifaceᵒ (HashIf^ω n)

oracle^ω : Systems HashIf^ω
oracle^ω = AtLevel.oracle

-- A hash implementation as a UC-level morphism, trivially graded, and the
-- ledger as a morphism OUT of the port.
hashᵒ : Systems HashIf^ω → (n : ℕ) → ifaceᵒ unitᴵ ⇒ T₀ 𝟘ᴳ (hashPortᵒ n)
hashᵒ hash n = closedᵒ (morphism (hash n))

ledgerᵒ : (n : ℕ) (vr : Variant) (s : Ledger.LState n)
        → hashPortᵒ n ⇒ T₀ 𝟘ᴳ (ifaceᵒ (LedgerIf^ω n))
ledgerᵒ n vr s = stageᵒ (morphism (AtLevel.ledger n vr s))

ledger-factor : (hash : Systems HashIf^ω) (vr : Variant) (n : ℕ) (s : Ledger.LState n)
              → closedᵒ (morphism (AtLevel.Sysᴴ n (hash n) vr s))
                ≈ sub λ⇒ ∘ (ledgerᵒ n vr s ∙ hashᵒ hash n)
ledger-factor hash vr n s = factorᵖ (AtLevel.ledger n vr s) (hash n)

-- The real family at an arbitrary hash, state schedule and variant.
Realᴴ : Systems HashIf^ω → Variant → ((n : ℕ) → Ledger.LState n) → Systems LedgerIf^ω
Realᴴ hash vr s n = AtLevel.Sysᴴ n (hash n) vr (s n)

open Budget budgetᵒ using (QB; qb-∘; qb-λ⇐)
open HomReasoning

module _ (vr : Variant) (s : (n : ℕ) → Ledger.LState n) where

  private
    -- The ledger as a family of homs out of the hash port, and what it costs
    -- that port: one call per transaction and none for an audit, plus the
    -- unit regrading `stageᵒ` puts in front of it.
    ledgerᶠ : Homᶠ (ifaceᶠ HashIf^ω) (Δ 𝟘ᴳ) (ifaceᶠ LedgerIf^ω)
    ledgerᶠ n = ledgerᵒ n vr (s n)

    ledgerᶠ-qb : (n : ℕ) → QB 1 (ledgerᶠ n)
    ledgerᶠ-qb n = qb-∘ qb-λ⇐ (qbᵒ (qb-ledger n (ser n) vr (s n)))

    factorᴿ : (hash : Systems HashIf^ω) (n : ℕ)
            → subᶠ (λ⇒ᶜ (Δ 𝟘ᴳ)) (ledgerᶠ ∙ᶠ imgᶠ HashIf^ω hash) n
              ≈ imgᶠ LedgerIf^ω (Realᴴ hash vr s) n
    factorᴿ hash n = ⟺ (ledger-factor hash vr n (s n))

  -- `≈ctx-ext` absorbs the ledger into the test at its own budget, `≈ctx-sub`
  -- the unit regrading, and `ledger-factor` reads both sides back as the
  -- closed systems `_≤UC^ωⁿ_` compares.  With one upper stage there is no
  -- simulator to compose, hence none to forget afterwards, which is what lets
  -- the corollary below go through (`docs/ledger-lift-eps.md` §§1, 5).
  hash-liftⁿ : (hash : Systems HashIf^ω) → hash ≤UC^ωⁿ oracle^ω
             → Realᴴ hash vr s ≤UC^ωⁿ Realᴴ oracle^ω vr s
  hash-liftⁿ hash (ε , neg , h) =
      εᴴ
    , NegligibleBound-simCost (λ _ → 1) (poly-const 1) ε₁
        (NegligibleBound-simCost (λ _ → 1) (poly-const 1) ε neg)
    , ≈ctx⇒≈ctxᴬ εᴴ
        (≈ctx-resp εᴴ (factorᴿ hash) (factorᴿ oracle^ω)
          (≈ctx-sub (λ⇒ᶜ (Δ 𝟘ᴳ)) ε₁
            (≈ctx-ext ledgerᶠ (λ _ → 1) ledgerᶠ-qb ε (≈ctxᴬ⇒≈ctx ε h))))
    where
    ε₁ εᴴ : ℕ → ℕ → ℚ
    ε₁ n q = ε n (simCost q 1)
    εᴴ n q = ε₁ n (simCost q 1)

-- Assume only that the hash function emulates the random oracle, and the
-- ledger built on it preserves value.
ledger-preserves-value-from-hash :
    (a V : ℕ) (hash : Systems HashIf^ω) → SerInj → hash ≤UC^ωⁿ oracle^ω
  → PreservesValue a V (Realᴴ hash inputConsuming (genesisAt a V))
ledger-preserves-value-from-hash a V hash si hp =
  preserves-value-transfer a V (Realᴴ hash inputConsuming (genesisAt a V)) si
    (hash-liftⁿ inputConsuming (genesisAt a V) hash hp)

------------------------------------------------------------------------
-- Claim 2: from the audit to the state trajectory
------------------------------------------------------------------------

-- Not the headline property, and not free.  UC identifies no internal state
-- trajectory, so a bound on one comes back only from the implementation's own
-- audit truthfulness — for a ledger image that is `Observable`'s theorem
-- (`ideal-truthful`), for anything else it is part of the statement — and the
-- instrumentation `withAudits`, which makes the watch see every boundary the
-- trajectory inspects, doubles the allowance.  That doubling is the cost of
-- the HONEST INTERFACE, charged in the conclusion's `λ n q → εᴸ n (q + q)`;
-- it is a different cost from the flag-reading a monitor compiler pays
-- (`docs/event-bounds-in-setup.md`), and the two are never netted against
-- each other.

module _ (a V : ℕ) where

  badᴸ : Bad (Ideal a V)
  badᴸ n = Watched.badTotal n (genesisAt a V n)

  TruthfulAudit : (R : Systems LedgerIf^ω) → Bad R → Set
  TruthfulAudit R bad = (n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
                      → PrHit (R n) (bad n) d
                        ℚ.≤ Pr (R n) (auditWatch a V n (Watched.withAudits n d))

  ideal-truthful : TruthfulAudit (Ideal a V) badᴸ
  ideal-truthful n =
    Watched.auditWatch-complete n (AtLevel.oracle n) inputConsuming (genesisAt a V n)

  ledger-uc-to-pov-family :
      SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
    → R ≤UC^ωⁿ Ideal a V → TruthfulAudit R badR
    → SaturatedHitᴺ R badR (λ n q → εᴸ n (q ℕ.+ q))
  ledger-uc-to-pov-family si R badR em truthful =
    saturatedHitᴺ-from-monitor {ε = εᴸ} {P = R} {Bad = badR} {bad = auditWatch a V}
      (λ _ q → q ℕ.+ q) Watched.withAudits (λ _ Pp → poly-+ Pp Pp)
      Watched.asks≤-withAudits truthful (preserves-value-transfer a V R si em)

  -- …read as one number: the real system's preservation-of-value failure is
  -- negligible in the security parameter at every polynomial allowance.
  ledger-pov-family-negligible :
      SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
    → R ≤UC^ωⁿ Ideal a V → TruthfulAudit R badR
    → (p : ℕ → ℕ) → Poly p
    → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
      × ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
         → asks≤ (p n) d → PrHit (R n) (badR n) d ℚ.≤ f n)
  ledger-pov-family-negligible si R badR em truthful p Pp =
    let νₚ , neg , bnd = ledger-uc-to-pov-family si R badR em truthful p Pp
    in (λ n → εᴸ n (p n ℕ.+ p n) ℚ.+ νₚ n)
     , Negligible-+ (εᴸ-negligible (λ n → p n ℕ.+ p n) (poly-+ Pp Pp)) neg
     , bnd

------------------------------------------------------------------------
-- Claim 3: the genesis is live
------------------------------------------------------------------------

module Live (a V n : ℕ) = Replay.Genesis n (ser n) (h₀ n) a V

-- Assumes nothing.  The pair is the acceptance and its state effect: the
-- genesis output IS spent, with probability one and through the oracle, and
-- its value reappears under the transaction's own hash.  A probability of 0
-- means nothing at a dead-locked ledger, which is what this rules out — but
-- one accepted transaction is not global liveness, and claims 1 and 2 do not
-- take it as a premise.
ideal-spends-genesis : (a V n : ℕ)
  → Pr (Ideal a V n) (Live.spend a V n) ≡ 1ℚ
  × ((h : Ledger.Hash n) → Live.moved a V n h ≡ (((h , 0) , (a , V)) ∷ [] , []))
ideal-spends-genesis a V n = Live.genesis-live a V n , Live.genesis-moves a V n

------------------------------------------------------------------------
-- What claims 1 and 2 do not say
------------------------------------------------------------------------

-- A ledger that diverges at every query satisfies claim 1 with ZERO slack and
-- never accepts anything: the observable bound does not imply responsiveness,
-- which is why that is claim 3's separate job and not a premise here.
Mute : Systems LedgerIf^ω
Mute n = record { St = ⊤ ; init = tt ; step = λ _ _ → dead }

-- …and one whose state is always bad while its answers never say so satisfies
-- claim 1 too, with its trajectory event at probability one.  The gap is
-- exactly `TruthfulAudit`, which claim 2 assumes and claim 1 does not.
Liar : Systems LedgerIf^ω
Liar n = record { St = ⊤ ; init = tt ; step = λ _ _ → ret (tt , AtLevel.ok false) }

always-bad : Bad Liar
always-bad _ _ = true

module _ (a V : ℕ) where

  private
    0≤εᴸ : (n q : ℕ) → 0ℚ ℚ.≤ εᴸ n q
    0≤εᴸ n q = 0≤* (0≤fromℕ (q ℕ.* q ℕ.+ q)) (0≤inv-pow-2 n)

    -- A watch that never reports is below every allowance, at slack 0.
    never-reports : (P : Systems LedgerIf^ω)
                  → ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
                     → Pr (P n) (auditWatch a V n d) ≡ 0ℚ)
                  → PreservesValue a V P
    never-reports P zero-pr p Pp = (λ _ → 0ℚ) , Negligible-0 , λ n d _ →
      subst (ℚ._≤ εᴸ n (p n) ℚ.+ 0ℚ) (sym (zero-pr n d))
            (subst (0ℚ ℚ.≤_) (sym (+-identityʳ (εᴸ n (p n)))) (0≤εᴸ n (p n)))

  mute-silent : (n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
              → Pr (Mute n) (auditWatch a V n d) ≡ 0ℚ
  mute-silent _ (out _)   = lookupᴰℚ-return (just false) mb
  mute-silent n (ask q k) =
    trans (>>=ᴹ-identityˡ nothing (kmaybe G) mb) (lookupᴰℚ-return nothing mb)
    where
    G : St (Mute n) × Pos (LedgerIf^ω n) → Dist⊥ Bool
    G st = runFrom (Mute n) (proj₁ st)
             (Watched.auditWatchFrom n (genesisAt a V n)
               (Watched.reportsLoss n (genesisAt a V n) q (proj₂ st)) (k (proj₂ st)))
  mute-silent n (coin μ k) =
    trans (E-bind μ (λ b → run (Mute n) (auditWatch a V n (k b))) mb)
          (trans (lookupᴰℚ-cong-P (entries μ) (λ b → mute-silent n (k b))) (E-const μ 0ℚ))

  mute-preserves-value : PreservesValue a V Mute
  mute-preserves-value = never-reports Mute mute-silent

  mute-never-accepts : (n : ℕ) → Pr (Mute n) (Live.spend a V n) ≡ 0ℚ
  mute-never-accepts n =
    trans (>>=ᴹ-identityˡ nothing (kmaybe G) mb) (lookupᴰℚ-return nothing mb)
    where
    G : St (Mute n) × Pos (LedgerIf^ω n) → Dist⊥ Bool
    G st = runFrom (Mute n) (proj₁ st) (out (AtLevel.accepted n (proj₂ st)))

  liar-quiet : (n : ℕ) (acc : Bool) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
             → Pr₁⊥ (runFrom (Liar n) tt (Watched.auditWatchFrom n (genesisAt a V n) acc d))
               ≡ bool→ℚ acc
  liar-quiet _ acc (out _)   = lookupᴰℚ-return (just acc) mb
  liar-quiet n acc (ask q k) =
    trans (>>=⊥-identityˡ (tt , ok false) G mb)
          (trans (cong atAcc (quiet q)) (liar-quiet n acc (k (ok false))))
    where
    open AtLevel n using (Query; submit; audit; ok)

    G : St (Liar n) × Pos (LedgerIf^ω n) → Dist⊥ Bool
    G st = runFrom (Liar n) (proj₁ st)
             (Watched.auditWatchFrom n (genesisAt a V n)
               (acc ∨ Watched.reportsLoss n (genesisAt a V n) q (proj₂ st)) (k (proj₂ st)))

    atAcc : Bool → ℚ
    atAcc b = Pr₁⊥ (runFrom (Liar n) tt
                (Watched.auditWatchFrom n (genesisAt a V n) b (k (ok false))))

    quiet : (q′ : Query) → acc ∨ Watched.reportsLoss n (genesisAt a V n) q′ (ok false) ≡ acc
    quiet (submit _) = ∨-identityʳ acc
    quiet audit      = ∨-identityʳ acc
  liar-quiet n acc (coin μ k) =
    trans (E-bind μ (λ b → runFrom (Liar n) tt
                             (Watched.auditWatchFrom n (genesisAt a V n) acc (k b))) mb)
          (trans (lookupᴰℚ-cong-P (entries μ) (λ b → liar-quiet n acc (k b)))
                 (E-const μ (bool→ℚ acc)))

  liar-preserves-value : PreservesValue a V Liar
  liar-preserves-value = never-reports Liar λ n → liar-quiet n false

  -- The same strategy at the same system: the trajectory event weighs one and
  -- the reported event zero, so no `TruthfulAudit` can hold of it.
  liar-not-truthful : ¬ TruthfulAudit a V Liar always-bad
  liar-not-truthful tr = 1≰0 (subst₂ ℚ._≤_ hits reports (tr 0 (out false)))
    where
    hits : PrHit (Liar 0) (always-bad 0) (out false) ≡ 1ℚ
    hits = lookupᴰℚ-return (just true) mb

    reports : Pr (Liar 0) (auditWatch a V 0 (Watched.withAudits 0 (out false))) ≡ 0ℚ
    reports = lookupᴰℚ-return (just false) mb
