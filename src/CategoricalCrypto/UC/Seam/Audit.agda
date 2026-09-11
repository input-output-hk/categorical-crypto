{-# OPTIONS --safe --without-K --guardedness #-}

-- The graded carry at the intended instance, and what it still owes layer 1.
--
-- `UC.Audit` proves the carry generically, over a base plus the two enrichment
-- data.  All three are now supplied rather than assumed: the base is the sealed
-- model (`UC.Model.Bridge.ucBaseᵒ`), and the budget and the mass are
-- `UC.Model.Enrichment`.  Nothing here is a parameter.
--
-- What remains open is the other end: an audit-watching STRATEGY has to be
-- recognized as one of the ancilla contexts the graded bound quantifies over,
-- which is `UC.Seam`'s embedding one grade up.
--
-- The two together are the ledger example's path: `audit-carry` moves
-- `POVaudit` from the ideal system to the real one across an emulation, and
-- `Examples.ChimericLedger.POV.TrajectoryFromAudit` turns the audit bound back
-- into the trajectory statement `POV`.  That is the route `pov-carry` takes
-- through direct agreement, with the simulator kept instead of collapsed.

open import Data.Nat.Base using (ℕ)
open import Data.Rational using (ℚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.Protocol.Observe using (Bounded)
open import CategoricalCrypto.Strategy using (Strat)
open import CategoricalCrypto.UC.Model.Bridge using (ucBaseᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ; massᵒ)
open import CategoricalCrypto.UC.Model.Seal using (ifaceᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup

import CategoricalCrypto.UC.Audit as Aud

module CategoricalCrypto.UC.Seam.Audit where

private module A = Aud ucBaseᵒ budgetᵒ massᵒ

open A public using (_≤UC[_]_; sim; sim-qb; emulate; simCost; AuditBound; audit-carry)

------------------------------------------------------------------------
-- What layer 1 still needs

module TrivialGrade (𝟘 : Channel) (ι : (B : Iface) → ifaceᵒ B ⇒ T₀ 𝟘 (ifaceᵒ B)) where

  -- The consumer end of the graded bound: at the trivial grade an audit-watching
  -- strategy, embedded as an environment, IS one of the contexts `AuditBound`
  -- quantifies over, so the graded bound restricts to layer 1's own `Bounded`.
  -- Stated and priced at ~120–180 LOC on top of `Adequacy`: the test is
  -- `UC.Seam.strategyEnv B (bad d)` plugged through the wires that kill `𝟘` and
  -- the `unitᴵ` ancilla, its certificate is the strategy's own ask-depth
  -- (`Counting`, at `ctxBudget q 1 = q`), and reading its mass as `Pr` is
  -- `PrAgree` — the same two obligations `agree-to-adv` rests on, one grade up.
  AuditIsBounded : Set₁
  AuditIsBounded = {B : Iface} (P : Protocol unitᴵ B)
                   (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) (ε : ℕ → ℚ)
                 → AuditBound (ι B ∘ procᵒ (morphism P)) ε
                 → Bounded P bad ε
