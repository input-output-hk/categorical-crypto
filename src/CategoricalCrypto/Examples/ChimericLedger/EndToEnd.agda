{-# OPTIONS --safe --without-K --guardedness #-}

-- The end-to-end asymptotic UC-to-POV theorem for the chimeric ledger.
--
-- `ledger-uc-to-pov` starts at the PROVED ideal birthday bound
-- (`ChimericLedger.Birthday.target`, read through the designated monitor by
-- `ChimericLedger.Trajectory`) and a genuine UC-emulation premise between the
-- real and ideal machine FAMILIES, and concludes a real-side bound on the
-- state trajectory — preservation of value — modulo negligible slack at every
-- polynomial allowance.  `ledger-pov-negligible` reads the same conclusion as
-- one number: at every polynomial allowance the real failure probability is
-- negligible, the birthday bound and the slack together.
--
-- What the theorem assumes, and nothing else:
--
--   `SerInj`        the birthday theorem's own injective-serialization
--                   hypothesis, per level (`Tx` depends on the hash width, so
--                   a single `ser` cannot be typed)
--   `R ≤UC^ω …`     the emulation, in the INHERITED preorder — a simulator per
--                   dummy adversary — never a direct `Agreeˢ`
--   `TotalRun`      on the real side; the ideal side's is proved
--                   (`ChimericLedger.Total`).  Not decoration: with the real
--                   side divergent every ideal is emulated, by a simulator
--                   that never starts
--   `TruthfulAudit` the real implementation's audit answers report its own
--                   state.  UC identifies no internal trajectory, so this is
--                   irreducibly about the implementation; for a ledger image
--                   it is `Trajectory.monitor-complete` and `ideal-truthful`
--                   supplies it
--
-- The costs are explicit and both appear in the conclusion: the audit
-- instrumentation doubles the allowance (`asks≤-audited`), and the slack is
-- `2⁻ⁿ`, negligible and positive (a carry off an ε-quantified agreement has no
-- zero instance to take).
--
-- `ledger-audit-carry` is the GRADED route beside it, where the simulator's
-- own query cost is charged (`simCost`).  It stops at an `AuditBound` rather
-- than a probability: see `UC.Asymptotic`'s header for why the two routes do
-- not compose.

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly; poly-+)
open import Data.Nat.Properties using (≤-refl)
open import Data.List.Base using (List)
open import Data.Bool.Base using (Bool)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)

open import ProbabilisticLogic.Distribution.Uniform using (inv-pow-2)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface using (Neg; Pos)
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.Protocol.Machine.Total using (TotalRun)
open import CategoricalCrypto.Protocol.Observe using (PrHit)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate using (Negligible; Negligible-+)
open import CategoricalCrypto.UC.Approximate.Decay
  using (0<inv-pow-2; negligible-slack)
open import CategoricalCrypto.UC.Asymptotic
open import CategoricalCrypto.UC.Model.Seal using (procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Saturated
  using (_≈negl_; Bad; SaturatedBoundedᴺ; SaturatedHitᴺ; Systems)
open import CategoricalCrypto.UC.Seam.Audit using (AuditBound; absorb; sim; simCost)
open import CategoricalCrypto.UC.Seam using (Agreeˢ)
open import CategoricalCrypto.UC.Seam.Grounded using (ιᴳ)

import CategoricalCrypto.Examples.ChimericLedger.Audit as Aud

module CategoricalCrypto.Examples.ChimericLedger.EndToEnd
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

open import CategoricalCrypto.Examples.ChimericLedger.Schedule ser

module Ad (n : ℕ) = Aud n (ser n)

private
  Strats : (n : ℕ) → Set
  Strats n = Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))

-- The slack the carries spend: `2⁻ⁿ`, positive at every level and negligible.
ν : ℕ → ℚ
ν = inv-pow-2

νNegligible : Negligible ν
νNegligible = negligible-slack λ _ → ≤-refl

------------------------------------------------------------------------
-- The theorem

-- For every polynomial allowance `p` there is a negligible `νₚ` such that no
-- strategy of budget `p n` moves the real system's total value away from
-- genesis with probability above `εbirthday` at the audit-adjusted allowance
-- plus `νₚ n`.
ledger-uc-to-pov :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
  → ((n : ℕ) → TotalRun (LedgerIf^ω n) (morphism (R n)))
  → R ≤UC^ω Ideal a V
  → TruthfulAudit a V R badR
  → SaturatedHitᴺ R badR (λ n q → εᴸ n (q ℕ.+ q))
ledger-uc-to-pov a V si R badR tR em truthful =
  saturatedHitᴺ-from-monitor {ε = εᴸ} {P = R} {Bad = badR} {bad = monitorᴸ a V}
    (λ _ q → q ℕ.+ q) (auditedᴸ a V) (λ _ Pp → poly-+ Pp Pp) (auditedᴸ-asks a V)
    truthful real
  where
  agree : (n : ℕ) → Agreeˢ (LedgerIf^ω n) (morphism (R n)) (morphism (Ideal a V n))
  agree = uc-agree {R = R} {I = Ideal a V} tR (idealTotal a V) em

  near : R ≈negl Ideal a V
  near = uc-≈negl {ν = ν} {R = R} {I = Ideal a V} 0<inv-pow-2 νNegligible agree

  ideal : SaturatedBoundedᴺ (Ideal a V) (monitorᴸ a V) εᴸ
  ideal = boundedᴺ {I = Ideal a V} {ε = εᴸ} {bad = monitorᴸ a V} (ideal-bounded a V si)

  real : SaturatedBoundedᴺ R (monitorᴸ a V) εᴸ
  real = uc-preservesᴺ {R = R} {I = Ideal a V} {ε = εᴸ} {bad = monitorᴸ a V}
           (monitorᴸ-preserving a V) near ideal

-- …read as one number: the real system's preservation-of-value failure is
-- negligible in the security parameter at every polynomial allowance.
ledger-pov-negligible :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
  → ((n : ℕ) → TotalRun (LedgerIf^ω n) (morphism (R n)))
  → R ≤UC^ω Ideal a V
  → TruthfulAudit a V R badR
  → (p : ℕ → ℕ) → Poly p
  → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
    × ((n : ℕ) (d : Strats n) → asks≤ (p n) d → PrHit (R n) (badR n) d ℚ.≤ f n)
ledger-pov-negligible a V si R badR tR em truthful p Pp =
  let νₚ , neg , bnd = ledger-uc-to-pov a V si R badR tR em truthful p Pp
  in (λ n → εᴸ n (p n ℕ.+ p n) ℚ.+ νₚ n)
   , Negligible-+ (εᴸ-negligible (λ n → p n ℕ.+ p n) (poly-+ Pp Pp)) neg
   , bnd

------------------------------------------------------------------------
-- The graded route

-- The same ideal bound crossing a BUDGETED emulation: the real side reads the
-- absorbed event class and the simulator's own queries are charged there.
ledger-audit-carry :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (cs : ℕ → ℕ)
    (em : R ≤UC^ω[ cs ] Ideal a V) (n : ℕ)
  → AuditBound (ιᴳ (LedgerIf^ω n) ∘ procᵒ (morphism (R n)))
      (absorb (sim (em n)) (cs n) (Ad.auditEvent n inputConsuming (gen a V n)))
      (λ q → εᴸ n (simCost q (cs n)) ℚ.+ ν n)
ledger-audit-carry a V si R cs em =
  uc-audit-carry {ε = εᴸ} {ν = ν} em (monitorᴸ a V)
    (λ n → Ad.audit-target n (h₀ n) (si n) a V) 0<inv-pow-2
