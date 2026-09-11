{-# OPTIONS --safe --without-K --guardedness #-}

-- The graded carry at the intended instance, its designated event, and what
-- the two owe layer 1.
--
-- `UC.Audit` proves the carry generically, over a base plus the two enrichment
-- data.  All three are now supplied rather than assumed: the base is the sealed
-- model (`UC.Model.Bridge.ucBaseᵒ`), and the budget and the mass are
-- `UC.Model.Enrichment`.  Nothing here is a parameter.
--
-- `watched` is the event the instance designates: not "whatever a budgeted test
-- reports" but "what the MONITOR reports", the monitor being the layer-1
-- strategy transformation `bad` whose truthfulness the example proves
-- (`Examples.ChimericLedger.Trajectory.monitor-sound`).  A context is permitted
-- when what it observes is that monitor's own verdict on an adversary its
-- budget affords, which is exactly what the embedded-strategy context of
-- `UC.Seam.Grounded` is.
--
-- Both directions are then statements about the same class, discharged in
-- `UC.Seam.Audit.Bounded`: `AuditIsBounded` extracts layer 1's `Bounded` from
-- the graded premise, and `BoundedIsAudit` SUPPLIES the graded premise from an
-- ordinary ideal bound — the direction `docs/protocol-implementation-review.md`
-- §1 found missing, and the reason the event is data.
--
-- The two together are the ledger example's path: `audit-carry` moves a
-- monitor bound from the ideal system to the real one across an emulation, and
-- `Examples.ChimericLedger.Trajectory` ties that bound to the trajectory
-- statement `POV` at both ends.

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ-syntax; _×_)
open import Data.Rational using (ℚ)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp using (_≈ₚ_)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Observe using (Bounded)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Model.Bridge using (ucBaseᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ; massᵒ)
open import CategoricalCrypto.UC.Model.Observation using (𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (ifaceᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup

import CategoricalCrypto.UC.Audit as Aud

module CategoricalCrypto.UC.Seam.Audit where

open import CategoricalCrypto.UC.Emulation ucBaseᵒ using (obs; tv₁)

private module A = Aud ucBaseᵒ budgetᵒ massᵒ

-- `audit-carry` is what this instantiation is FOR, so it is re-exported even
-- with no consumer yet; the rest of `UC.Audit`'s plumbing is reached from there.
open A public using (AuditEvent; AuditBound; audit-carry)

------------------------------------------------------------------------
-- The consumer end

module TrivialGrade (𝟘 : Channel) (ι : (B : Iface) → ifaceᵒ B ⇒ T₀ 𝟘 (ifaceᵒ B)) where

  -- The event `P` designates under the monitor `bad`: a context reads it when
  -- what it observes IS the monitor's verdict on an adversary of the context's
  -- own budget.  Nothing here quantifies over arbitrary verdicts — a test that
  -- reports `true` without asking is not a monitor of anything, and admitting
  -- it is what made the previous premise uninhabitable (implementation review
  -- §1).  What makes the designation TRUSTED is the monitor's truthfulness,
  -- which is the instance's theorem and not a datum of this layer.
  watched : {B : Iface} (P : Protocol unitᴵ B)
            (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B))
          → AuditEvent 0ℓ 𝟘ᵒ 𝟘 (ifaceᵒ B)
  watched {B} P bad Y Et m q =
    Σ[ d ∈ Strat (Neg B) (Pos B) ] asks≤ q d
      × obs (tv₁ Y (ι B ∘ procᵒ (morphism P)) Et) m ≈ₚ runᴹ (morphism P) (bad d)

  -- At the trivial grade an audit-watching strategy, embedded as an
  -- environment, IS one of the contexts the event permits, so the graded bound
  -- restricts to layer 1's own `Bounded`.  Proved at `𝟘 = unit` in
  -- `UC.Seam.Audit.Bounded`, whose header has the three ingredients.
  --
  -- The `bad`-budget hypothesis is the one the route already needs and the
  -- statement omitted: `Bounded P bad ε` charges `ε` at the budget of `d`,
  -- while the context that observes the event is built from `bad d`, so the
  -- graded bound can only be instantiated at a budget `bad d` is known to
  -- afford.  It is the hypothesis `Protocol.Observe.transfer`,
  -- `UC.Seam.pov-carry` and `Examples.ChimericLedger.pov-transfer` all carry.
  AuditIsBounded : Set₁
  AuditIsBounded = {B : Iface} (P : Protocol unitᴵ B)
                   (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) (ε : ℕ → ℚ)
                 → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → asks≤ q (bad d))
                 → AuditBound (ι B ∘ procᵒ (morphism P)) (watched P bad) ε
                 → Bounded P bad ε

  -- …and back: an ideal bound on the monitor's verdict supplies the graded
  -- premise, no budget hypothesis needed — the permitted context carries the
  -- adversary its budget affords.  This is the direction an emulation consumes
  -- (`audit-carry`), and its existence is what makes the premise a statement
  -- about the designated event rather than about every verdict.
  BoundedIsAudit : Set₁
  BoundedIsAudit = {B : Iface} (P : Protocol unitᴵ B)
                   (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) (ε : ℕ → ℚ)
                 → Bounded P bad ε
                 → AuditBound (ι B ∘ procᵒ (morphism P)) (watched P bad) ε
