{-# OPTIONS --safe --without-K --guardedness #-}

-- The hash-level premise lifted to the ledger WITH ITS ERROR, and the POV
-- corollary off it.
--
-- `ChimericLedger.Factor` lifts the QUALITATIVE premise `hash ≤UC^ω oracle^ω`
-- and only then meets the quantitative layer; here the ε crosses the factoring.
-- Two lifts, because the two premise shapes want different laws:
--
--   `hash-liftᵉ`  the canonical witness `_≤UC^ωᵉ_` at the hash port, carried by
--                 `UC.Asymptotic.Compose.UC-composeᵉ` and regraded by
--                 `≤UC^ωᵉ-sub`.  Everything it demands is DISCHARGED here: the
--                 ledger's own query bound (`ChimericLedger.QueryBound`), the
--                 hash's (`UC.QueryBound.qb-closed` — a closed process has no
--                 downward output at all), and `Allowance-mono` at the ledger's
--                 schedule, which is zero because the two sides share their
--                 upper stage.
--   `hash-liftⁿ`  the direct-agreement specialization `_≤UC^ωⁿ_`, carried by
--                 `≈ctx-ext` and `≈ctx-sub` alone.  With one upper stage there
--                 is no simulator to compose, hence none to forget afterwards,
--                 which is what lets the POV corollary go through.
--
-- The honest premise shape at this port is the `ωⁿ` one, and not by fiat:
-- `POV.oracle` exposes no adversary interface, so the hash boundary is graded
-- at `𝟘ᴳ` on both sides and every simulator there is a scalar
-- (`docs/ledger-factoring.md`).  `≤UC^ωⁿ⇒≤UC^ωᵉ` is the inclusion, so
-- `hash-liftᵉ` covers it and more; what the `ᵉ` route cannot do at this
-- application is END — forgetting a witness back into direct agreement needs
-- its simulator to act trivially, which at a general simulator is
-- `UC.Seam.Grounded.subBlind` and costs the real side's totality
-- (`docs/ledger-lift-eps.md`).

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Poly using (Poly; poly-const)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (≤-refl)
open import Level using (Level)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Examples.ChimericLedger.QueryBound using (qb-ledger)
open import CategoricalCrypto.Iface using (Neg; Pos)
open import CategoricalCrypto.Protocol.Live using (NoDeadStep; live)
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.Protocol.Machine.Total using (TotalRun; totalRun-morphism)
open import CategoricalCrypto.Protocol.Observe using (PrHit)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate using (Negligible; Negligible-0)
open import CategoricalCrypto.UC.Asymptotic using (_≤UC^ω_)
open import CategoricalCrypto.UC.Asymptotic.Compose
open import CategoricalCrypto.UC.Asymptotic.Contextual
open import CategoricalCrypto.UC.Asymptotic.Family
  using (_≤UC^ωⁿ_; ifaceᶠ; imgᶠ; uc-≤UC^ωⁿ)
open import CategoricalCrypto.UC.Budget using (Budget; simCost)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ; qbᵒ)
open import CategoricalCrypto.UC.Model.Family using (Δ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound using (qb-closed)
open import CategoricalCrypto.UC.Saturated using (Bad; Systems)
open import CategoricalCrypto.UC.Seam.Grounded using (𝟘ᴳ)

module CategoricalCrypto.Examples.ChimericLedger.FactorEps
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

open import CategoricalCrypto.Examples.ChimericLedger.EndToEnd ser
open import CategoricalCrypto.Examples.ChimericLedger.Factor ser
open import CategoricalCrypto.Examples.ChimericLedger.Real ser
open import CategoricalCrypto.Examples.ChimericLedger.Schedule ser

open Budget budgetᵒ using (QB; qb-∘; qb-λ⇐)
open HomReasoning

------------------------------------------------------------------------
-- The two stages' query bounds

-- A closed process makes no downward output at all, so the hash costs the
-- context nothing whatever it is: this is `qb-closed`, and it is why the lift
-- carries no polynomial-cost premise about the hash.
hash-qb : (hash : Systems HashIf^ω) (n : ℕ) → QB 0 (imgᶠ HashIf^ω hash n)
hash-qb hash n = qb-∘ qb-λ⇐ (qbᵒ (qb-closed (morphism (hash n))))

------------------------------------------------------------------------
-- The lifts

module _ (vr : Variant) (s : (n : ℕ) → Ledger.LState n) where

  -- The ledger as a family of homs OUT of the hash port.
  ledgerᶠ : Homᶠ (ifaceᶠ HashIf^ω) (Δ 𝟘ᴳ) (ifaceᶠ LedgerIf^ω)
  ledgerᶠ n = ledgerᵒ n vr (s n)

  -- One hash call per transaction and none for an audit, plus the unit
  -- regrading `stageᵒ` puts in front of it.
  ledgerᶠ-qb : (n : ℕ) → QB 1 (ledgerᶠ n)
  ledgerᶠ-qb n = qb-∘ qb-λ⇐ (qbᵒ (qb-ledger n (ser n) vr (s n)))

  private
    factorᴿ : (hash : Systems HashIf^ω) (n : ℕ)
            → subᶠ (λ⇒ᶜ (Δ 𝟘ᴳ)) (ledgerᶠ ∙ᶠ imgᶠ HashIf^ω hash) n
              ≈ imgᶠ LedgerIf^ω (Realᴴ hash vr s) n
    factorᴿ hash n = ⟺ (ledger-factor hash vr n (s n))

  -- The ε-retaining lift, at the canonical witness: the hash's simulator is
  -- composed with the ledger's — which is the identity, the upper stage being
  -- shared — and regraded by the unit `_∙ᶠ_` introduced.
  hash-liftᵉ : (hash : Systems HashIf^ω)
             → imgᶠ HashIf^ω hash ≤UC^ωᵉ imgᶠ HashIf^ω oracle^ω
             → imgᶠ LedgerIf^ω (Realᴴ hash vr s)
               ≤UC^ωᵉ imgᶠ LedgerIf^ω (Realᴴ oracle^ω vr s)
  hash-liftᵉ hash (sf , εf , nf , ef) =
    ≤UC^ωᵉ-resp (factorᴿ hash) (factorᴿ oracle^ω)
      (≤UC^ωᵉ-sub (λ⇒ᶜ (Δ 𝟘ᴳ)) (λ⇐ᶜ (Δ 𝟘ᴳ)) (λ _ → unitorˡ.isoˡ)
        (UC-composeᵉ sf εf nf ef
                     idᶜ (λ _ _ → 0ℚ) (λ _ _ → Negligible-0) (λ _ _ → ≤-refl)
                     (≈C⇒≈ctx λ n → Equiv.sym (sub-identityˡ (ledgerᶠ n)))
                     (λ _ → 0) (poly-const 0) (hash-qb hash)
                     (λ _ → 1) (poly-const 1) ledgerᶠ-qb))

  -- …and at the direct-agreement premise, where there is no simulator at all:
  -- `≈ctx-ext` absorbs the ledger into the test at its own budget, `≈ctx-sub`
  -- the unit regrading, and `ledger-factor` reads both sides back as the closed
  -- systems `_≤UC^ωⁿ_` compares.
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

------------------------------------------------------------------------
-- The POV corollary, at a hash-level premise that keeps its error

module _ (a V : ℕ) (hash : Systems HashIf^ω) where

  Realᵉ : Systems LedgerIf^ω
  Realᵉ = Realᴴ hash inputConsuming (gen a V)

  badᵉ : Bad Realᵉ
  badᵉ n = L.badTotal n (gen a V n)

  -- `Real.real-truthful` at this naming of the same family: an audit answer
  -- reports the LEDGER's state whatever it hashes with.
  truthfulᵉ : TruthfulAudit a V Realᵉ badᵉ
  truthfulᵉ n = T.monitor-complete n (hash n) inputConsuming (gen a V n)

  -- `Real.ledger-pov`'s conclusion from an ε-RETAINING premise about the hash
  -- alone.  Neither `TotalRun` nor `NoDeadStep` appears: the pointwise theorem
  -- spends totality to collapse an emulation into an agreement, and there is
  -- nothing here to collapse.
  ledger-pov-from-hashⁿ : SerInj → hash ≤UC^ωⁿ oracle^ω → (p : ℕ → ℕ) → Poly p
                        → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
                          × ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
                             → asks≤ (p n) d → PrHit (Realᵉ n) (badᵉ n) d ℚ.≤ f n)
  ledger-pov-from-hashⁿ si hp =
    ledger-pov-family-negligible a V si Realᵉ badᵉ
      (hash-liftⁿ inputConsuming (gen a V) hash hp) truthfulᵉ

------------------------------------------------------------------------
-- …and the qualitative corollary derived from it

-- `Factor.ledger-pov-from-hash` verbatim, off the ε-retaining route instead of
-- off `UC.Factor.liftᵖ`: the pointwise premise includes into the family one
-- (`uc-≤UC^ωⁿ`, at the hash's own liveness), the error is carried through the
-- factoring, and only the family theorem's own carry forgets it.  So the two
-- routes prove the same statement and the migration costs nothing.
module _ (a V : ℕ) (hash : Systems HashIf^ω) (nd : (n : ℕ) → NoDeadStep (hash n)) where

  ledger-pov-from-hash′ : SerInj → hash ≤UC^ω oracle^ω → (p : ℕ → ℕ) → Poly p
                        → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
                          × ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
                             → asks≤ (p n) d
                             → PrHit (Real a V inputConsuming hash nd n)
                                     (badReal a V inputConsuming hash nd n) d ℚ.≤ f n)
  ledger-pov-from-hash′ si hp = ledger-pov-from-hashⁿ a V hash si (uc-≤UC^ωⁿ tHash hp)
    where
    tHash : (n : ℕ) → TotalRun (HashIf^ω n) (morphism (hash n))
    tHash n = totalRun-morphism (HashIf^ω n) (hash n) (live (hash n) (nd n))

  private
    at : {ℓ : Level} {A : Set ℓ} → A → A → A
    at _ x = x

    -- The statement above is `Factor.ledger-pov-from-hash`'s OWN and not a copy
    -- of it: this stops checking the moment the two drift apart.
    migration-pin : _
    migration-pin = at (ledger-pov-from-hash a V hash nd) ledger-pov-from-hash′
