{-# OPTIONS --safe --without-K --guardedness #-}

-- Preservation of value transported across a UC emulation.
--
-- `preserves-value-transfer` is the whole point of the example: the ideal
-- birthday bound plus an emulation premise give the SAME property about the
-- real system, with no further hypothesis.
--
-- `R ≤UC^ωⁿ I` is an allowance-uniform emulation with negligible error.
--
-- The appendix restates the conclusion over R's own STATE TRAJECTORY, which
-- needs one extra hypothesis (`TruthfulAudit`) because UC identifies no
-- internal state.

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Asymptotic
open import CategoricalCrypto.UC.Asymptotic.Family
open import CategoricalCrypto.UC.Saturated

module CategoricalCrypto.Examples.ChimericLedger.EndToEnd
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

open import CategoricalCrypto.Examples.ChimericLedger.Schedule ser

private
  Strats : (n : ℕ) → Set
  Strats n = Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n))

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

module _ (a V : ℕ) where

  preserves-value-transfer : (R : Systems LedgerIf^ω) → SerInj
                           → R ≤UC^ωⁿ Ideal a V → PreservesValue a V R
  preserves-value-transfer R si em =
    uc-preservesᴺ {R = R} {I = Ideal a V} {ε = εᴸ} {bad = monitorᴸ a V}
      (monitorᴸ-preserving a V) (≤UC^ωⁿ⇒≈negl {R = R} {I = Ideal a V} em)
      (ideal-preserves-value a V si)

------------------------------------------------------------------------
-- APPENDIX: the same conclusion about the real system's own states
------------------------------------------------------------------------

-- Not the headline property, and not free: UC identifies no internal state
-- trajectory, so a bound on one is recovered only from the implementation's
-- own audit truthfulness, and the audit instrumentation that makes the watch
-- see every boundary doubles the allowance (`asks≤-audited`).

  ledger-uc-to-pov-family :
      SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
    → R ≤UC^ωⁿ Ideal a V
    → TruthfulAudit a V R badR
    → SaturatedHitᴺ R badR (λ n q → εᴸ n (q ℕ.+ q))
  ledger-uc-to-pov-family si R badR em truthful =
    saturatedHitᴺ-from-monitor {ε = εᴸ} {P = R} {Bad = badR} {bad = monitorᴸ a V}
      (λ _ q → q ℕ.+ q) (auditedᴸ a V) (λ _ Pp → poly-+ Pp Pp) (auditedᴸ-asks a V)
      truthful (preserves-value-transfer R si em)

  -- …read as one number: the real system's preservation-of-value failure is
  -- negligible in the security parameter at every polynomial allowance.
  ledger-pov-family-negligible :
      SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
    → R ≤UC^ωⁿ Ideal a V
    → TruthfulAudit a V R badR
    → (p : ℕ → ℕ) → Poly p
    → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
      × ((n : ℕ) (d : Strats n) → asks≤ (p n) d → PrHit (R n) (badR n) d ℚ.≤ f n)
  ledger-pov-family-negligible si R badR em truthful p Pp =
    let νₚ , neg , bnd = ledger-uc-to-pov-family si R badR em truthful p Pp
    in (λ n → εᴸ n (p n ℕ.+ p n) ℚ.+ νₚ n)
     , Negligible-+ (εᴸ-negligible (λ n → p n ℕ.+ p n) (poly-+ Pp Pp)) neg
     , bnd
