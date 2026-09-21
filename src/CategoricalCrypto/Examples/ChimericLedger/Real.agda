{-# OPTIONS --safe --without-K --guardedness #-}

-- The end-to-end theorem at a REAL ledger: the same ledger code, hashing with
-- an implementation instead of the random oracle.
--
--     Real n = ledger inputConsuming (genesis n) ∘ᵖ hash n
--     Ideal  = the same, with `ChimericLedger.POV.oracle` in place of `hash n`
--
-- `ledger-uc-to-pov`'s three hypotheses about the real family (`Bad`,
-- `TotalRun`, `TruthfulAudit`) are discharged here once and generically in the
-- hash, of which only `NoDeadStep` is then assumed; the emulation and the
-- birthday theorem's `SerInj` are what is left (`docs/end-to-end.md` §3).

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Poly using (Poly)
open import Data.Product.Base using (Σ-syntax; _×_)
open import Data.Rational as ℚ using (ℚ)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface using (Neg; Pos; unitᴵ)
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Live using (NoDeadStep)
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.Protocol.Machine.Total using (TotalRun)
open import CategoricalCrypto.Protocol.Observe using (PrHit)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate using (Negligible)
open import CategoricalCrypto.UC.Asymptotic using (_≤UC^ω_)
open import CategoricalCrypto.UC.Saturated using (Bad; Systems)

module CategoricalCrypto.Examples.ChimericLedger.Real
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

open import CategoricalCrypto.Examples.ChimericLedger.EndToEnd ser
open import CategoricalCrypto.Examples.ChimericLedger.Schedule ser

-- `hash n` is the hash at security parameter `n`, on the ledger's own hash
-- interface; `vr` is the ledger's variant, `inputConsuming` being the one the
-- ideal side's bound is proved at (`ChimericLedger.Birthday`).
module _ (a V : ℕ) (vr : Variant)
         (hash : (n : ℕ) → Protocol unitᴵ (L.HashIf n)) where

  Real : Systems LedgerIf^ω
  Real n = L.Sysᴴ n (hash n) vr (gen a V n)

  -- The POV event: some reached state's total value differs from genesis.
  badReal : Bad Real
  badReal n = L.badTotal n (gen a V n)

  real-truthful : TruthfulAudit a V Real badReal
  real-truthful n = T.monitor-complete n (hash n) vr (gen a V n)

  module _ (nd : (n : ℕ) → NoDeadStep (hash n)) where

    realTotal : (n : ℕ) → TotalRun (LedgerIf^ω n) (morphism (Real n))
    realTotal n = Tt.totalRun-Sys n (hash n) (nd n) vr (gen a V n)

    -- The slides' claim: the emulation and the injective serialization, in; a
    -- negligible bound on the real ledger's loss of value, out.  The number is
    -- `ledger-pov-negligible`'s, the birthday bound at the audit-adjusted
    -- allowance plus the carry's slack: `((2·p n)² + 2·p n)·2⁻ⁿ + νₚ n`.
    ledger-pov : SerInj → Real ≤UC^ω Ideal a V → (p : ℕ → ℕ) → Poly p
               → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
                 × ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
                    → asks≤ (p n) d → PrHit (Real n) (badReal n) d ℚ.≤ f n)
    ledger-pov si em =
      ledger-pov-negligible a V si Real badReal realTotal em real-truthful
