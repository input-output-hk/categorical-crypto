{-# OPTIONS --safe --without-K --guardedness #-}

-- The UC layer's audit premise at the ideal ledger, supplied.
--
-- `UC.Seam.Audit`'s graded bound is about a DESIGNATED event, and this is the
-- designation for the ledger: the contexts reading `monitor`, the strategy
-- transformation whose verdict `ChimericLedger.Trajectory` proves is exactly
-- the trajectory violation (sound by `monitor-sound`, complete on audited
-- strategies by `monitor-complete`).
--
-- `audit-target` is the acceptance test of that interface: the ideal system's
-- PROVED birthday bound — a statement about state trajectories, with no UC
-- vocabulary in it — is turned into the premise `audit-carry` consumes, with
-- no hypothesis added along the way.  The previous premise had no such supply
-- and could not have one (`docs/protocol-implementation-review.md` §1).
--
-- What is NOT here is the emulation: carrying this premise to a real system
-- needs `f ≤UC[ cs ] g` between machine images and a real-side event class
-- absorbing into this one, and neither is built (review §4).

open import Data.Bool.Base using (Bool; false)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)
open import Data.Rational using (ℚ)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.UC.Model.Observation using (𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (ifaceᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam.Audit
  using (AuditEvent; AuditBound; module TrivialGrade)
open import CategoricalCrypto.UC.Seam.Audit.Bounded
  using (auditIsBounded; boundedIsAudit)
open import CategoricalCrypto.UC.Seam.Grounded using (𝟘ᴳ; ιᴳ)

module CategoricalCrypto.Examples.ChimericLedger.Audit
  (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) where

open Ledger ℓ

open import CategoricalCrypto.Examples.ChimericLedger.Birthday ℓ ser using (target)
open import CategoricalCrypto.Examples.ChimericLedger.POV ℓ ser
open import CategoricalCrypto.Examples.ChimericLedger.Trajectory ℓ ser
  using (monitor-bounded)

private module TG = TrivialGrade 𝟘ᴳ ιᴳ

-- The ledger's designated audit event: the contexts that read what `monitor`
-- reports, at the adversary budget they afford it.
auditEvent : (vr : Variant) (s₀ : LState) → AuditEvent 0ℓ 𝟘ᵒ 𝟘ᴳ (ifaceᵒ LedgerIf)
auditEvent vr s₀ = TG.watched (Sys vr s₀) (monitor s₀)

-- …and the graded premise about it, from the monitor's own bound.
audit-bound : (vr : Variant) (s₀ : LState) {ε : ℕ → ℚ} → POVmonitor vr s₀ ε
            → AuditBound (ιᴳ LedgerIf ∘ procᵒ (morphism (Sys vr s₀))) (auditEvent vr s₀) ε
audit-bound vr s₀ {ε} = boundedIsAudit (Sys vr s₀) (monitor s₀) ε

-- …and back, so the graded premise is no stronger than the ideal bound that
-- supplies it: at the trivial grade the two are the same statement.
audit-bounded : (vr : Variant) (s₀ : LState) {ε : ℕ → ℚ}
              → AuditBound (ιᴳ LedgerIf ∘ procᵒ (morphism (Sys vr s₀))) (auditEvent vr s₀) ε
              → POVmonitor vr s₀ ε
audit-bounded vr s₀ {ε} =
  auditIsBounded (Sys vr s₀) (monitor s₀) ε (λ q d → asks≤-monitor s₀ q false d)

-- The acceptance test: the proved birthday theorem, and nothing else.
audit-target : (h₀ : Hash) (ser-inj : {t u : Tx} → ser t ≡ ser u → t ≡ u)
               (a : Addr) (V : ℕ)
             → let s₀ = genesis h₀ a V in
               AuditBound (ιᴳ LedgerIf ∘ procᵒ (morphism (Sys inputConsuming s₀)))
                          (auditEvent inputConsuming s₀) (AtBirthday.εbirthday h₀ ser-inj)
audit-target h₀ ser-inj a V =
  audit-bound inputConsuming s₀ (monitor-bounded inputConsuming s₀ (target h₀ ser-inj a V))
  where s₀ = genesis h₀ a V
