{-# OPTIONS --safe --without-K --guardedness #-}

-- The end-to-end asymptotic UC-to-POV theorem for the chimeric ledger.
--
-- `ledger-uc-to-pov-family` starts at the PROVED ideal birthday bound
-- (`ChimericLedger.Birthday.target`, read through the designated monitor by
-- `ChimericLedger.Trajectory`) and a genuine UC-emulation premise between the
-- real and ideal machine FAMILIES, and concludes a real-side bound on the
-- state trajectory — preservation of value — modulo negligible slack at every
-- polynomial allowance.  `ledger-pov-family-negligible` reads the same
-- conclusion as one number: at every polynomial allowance the real failure
-- probability is negligible, the birthday bound and the slack together.
--
-- What the theorem assumes, and nothing else:
--
--   `SerInj`        the birthday theorem's own injective-serialization
--                   hypothesis, per level (`Tx` depends on the hash width, so
--                   a single `ser` cannot be typed)
--   `R ≤UC^ωⁿ …`    the emulation, allowance-uniform and quantitative, never a
--                   direct `Agreeˢ`
--   `TruthfulAudit` the real implementation's audit answers report its own
--                   state.  UC identifies no internal trajectory, so this is
--                   irreducibly about the implementation; for a ledger image
--                   it is `Trajectory.monitor-complete` and `ideal-truthful`
--                   supplies it
--
-- `ledger-uc-to-pov`/`ledger-pov-negligible` are the same two statements at
-- the pointwise premise `_≤UC^ω_` plus the real side's `TotalRun`, which
-- `uc-≤UC^ωⁿ` includes into the family one.  That totality is not decoration:
-- with the real side divergent every ideal is emulated, by a simulator that
-- never starts.
--
-- The cost is explicit and appears in the conclusion: the audit
-- instrumentation doubles the allowance (`asks≤-audited`).
--
-- A BUDGETED premise `_≤UC^ω[ cs ]_` reaches the same conclusion through
-- `UC.Seam.Audit.Prefix`, at the worse allowance `simCost (q + q) (cs n)`.
-- That route was retired 2026-09-21: a budgeted emulation IS an emulation
-- (`UC.Audit.Canonical.audit-forget` after `audit⇒witness`), so these theorems
-- already apply wherever it did and give the sharper bound — at the trivial
-- grade the simulator costs the ideal side nothing.

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly; poly-+)
open import Data.List.Base using (List)
open import Data.Bool.Base using (Bool)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface using (Neg; Pos)
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.Protocol.Machine.Total using (TotalRun)
open import CategoricalCrypto.Protocol.Observe using (PrHit)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate using (Negligible; Negligible-+)
open import CategoricalCrypto.UC.Asymptotic
open import CategoricalCrypto.UC.Asymptotic.Family
  using (_≤UC^ωⁿ_; uc-≤UC^ωⁿ; ≤UC^ωⁿ⇒≈negl)
open import CategoricalCrypto.UC.Saturated
  using (_≈negl_; Bad; SaturatedBoundedᴺ; SaturatedHitᴺ; Systems)

module CategoricalCrypto.Examples.ChimericLedger.EndToEnd
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

open import CategoricalCrypto.Examples.ChimericLedger.Schedule ser

private
  Strats : (n : ℕ) → Set
  Strats n = Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))

------------------------------------------------------------------------
-- The theorem

-- For every polynomial allowance `p` there is a negligible `νₚ` such that no
-- strategy of budget `p n` moves the real system's total value away from
-- genesis with probability above `εbirthday` at the audit-adjusted allowance
-- plus `νₚ n`.  The premise is the asymptotic-family one
-- (`UC.Asymptotic.Family._≤UC^ωⁿ_`): an ε-approximate family emulation whose ε
-- is retained and negligible at every polynomial allowance.  Three things are
-- worth reading off the statement.
--
--   The BOUND keeps no ε of the premise.  `≈negl-respects` folds it into the
--   saturated slack rather than into `ε`, and the slack is quantified after the
--   allowance, so the birthday term is `εᴸ n (q + q)` — the audit
--   instrumentation's doubling and nothing else.
--
--   There is no `TotalRun`.  The pointwise specialization below spends one to
--   collapse a per-level emulation into an agreement (a divergent real side is
--   emulated by a simulator that never starts); the family premise is already
--   quantitative, so there is nothing to collapse.
--
--   No EXACT agreement is passed through.  `Agreeˢ` appears nowhere in this
--   proof: the ε travels contextual → direct-run
--   (`UC.Asymptotic.Family.≈ᶠ-runs`, over `UC.Seam.Audit.Context`) → `_≈negl_`
--   → `SaturatedBoundedᴺ`, which is review §1's acceptance condition.
ledger-uc-to-pov-family :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
  → R ≤UC^ωⁿ Ideal a V
  → TruthfulAudit a V R badR
  → SaturatedHitᴺ R badR (λ n q → εᴸ n (q ℕ.+ q))
ledger-uc-to-pov-family a V si R badR em truthful =
  saturatedHitᴺ-from-monitor {ε = εᴸ} {P = R} {Bad = badR} {bad = monitorᴸ a V}
    (λ _ q → q ℕ.+ q) (auditedᴸ a V) (λ _ Pp → poly-+ Pp Pp) (auditedᴸ-asks a V)
    truthful real
  where
  near : R ≈negl Ideal a V
  near = ≤UC^ωⁿ⇒≈negl {R = R} {I = Ideal a V} em

  ideal : SaturatedBoundedᴺ (Ideal a V) (monitorᴸ a V) εᴸ
  ideal = boundedᴺ {I = Ideal a V} {ε = εᴸ} {bad = monitorᴸ a V} (ideal-bounded a V si)

  real : SaturatedBoundedᴺ R (monitorᴸ a V) εᴸ
  real = uc-preservesᴺ {R = R} {I = Ideal a V} {ε = εᴸ} {bad = monitorᴸ a V}
           (monitorᴸ-preserving a V) near ideal

-- …read as one number: the real system's preservation-of-value failure is
-- negligible in the security parameter at every polynomial allowance.
ledger-pov-family-negligible :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
  → R ≤UC^ωⁿ Ideal a V
  → TruthfulAudit a V R badR
  → (p : ℕ → ℕ) → Poly p
  → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
    × ((n : ℕ) (d : Strats n) → asks≤ (p n) d → PrHit (R n) (badR n) d ℚ.≤ f n)
ledger-pov-family-negligible a V si R badR em truthful p Pp =
  let νₚ , neg , bnd = ledger-uc-to-pov-family a V si R badR em truthful p Pp
  in (λ n → εᴸ n (p n ℕ.+ p n) ℚ.+ νₚ n)
   , Negligible-+ (εᴸ-negligible (λ n → p n ℕ.+ p n) (poly-+ Pp Pp)) neg
   , bnd

------------------------------------------------------------------------
-- …off the POINTWISE premise

-- The same two statements at `UC.Asymptotic._≤UC^ω_` plus the real side's
-- totality.  `uc-≤UC^ωⁿ` is the whole of the difference: it puts that pair into
-- the family premise, at the schedule `2⁻ⁿ`, so these are the family theorems
-- at a strictly stronger hypothesis and not a second route.
ledger-uc-to-pov :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
  → ((n : ℕ) → TotalRun (LedgerIf^ω n) (morphism (R n)))
  → R ≤UC^ω Ideal a V
  → TruthfulAudit a V R badR
  → SaturatedHitᴺ R badR (λ n q → εᴸ n (q ℕ.+ q))
ledger-uc-to-pov a V si R badR tR em =
  ledger-uc-to-pov-family a V si R badR (uc-≤UC^ωⁿ tR em)

ledger-pov-negligible :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
  → ((n : ℕ) → TotalRun (LedgerIf^ω n) (morphism (R n)))
  → R ≤UC^ω Ideal a V
  → TruthfulAudit a V R badR
  → (p : ℕ → ℕ) → Poly p
  → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
    × ((n : ℕ) (d : Strats n) → asks≤ (p n) d → PrHit (R n) (badR n) d ℚ.≤ f n)
ledger-pov-negligible a V si R badR tR em =
  ledger-pov-family-negligible a V si R badR (uc-≤UC^ωⁿ tR em)
