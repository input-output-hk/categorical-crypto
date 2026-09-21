{-# OPTIONS --safe --without-K --guardedness #-}

-- Preservation of value, carried across a UC emulation.
--
-- `preserves-value-transfer` is the point of the example: the proved ideal
-- bound plus an emulation premise give the SAME property about the real
-- system, with nothing else assumed.  `R ≤UC^ωⁿ I` is an allowance-uniform
-- emulation with negligible error.
--
-- `ledger-preserves-value-from-hash` is the slides' last step: the premise
-- may be about the HASH alone, because the closed system factors through a
-- hash port.  The appendix restates the conclusion over the real system's own
-- state trajectory, which costs one extra hypothesis.

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Examples.ChimericLedger.QueryBound
open import CategoricalCrypto.Iface
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

module CategoricalCrypto.Examples.ChimericLedger.Transfer
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

open import CategoricalCrypto.Examples.ChimericLedger.Property ser

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

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
-- APPENDIX: the same conclusion about the real system's own states
------------------------------------------------------------------------

-- Not the headline property, and not free.  UC identifies no internal state
-- trajectory, so a bound on one comes back only from the implementation's own
-- audit truthfulness — for a ledger image that is `Observable`'s theorem, for
-- anything else it is part of the statement — and the instrumentation that
-- makes the watch see every boundary the trajectory inspects doubles the
-- allowance.

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
