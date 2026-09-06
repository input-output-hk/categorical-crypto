{-# OPTIONS --safe --without-K --guardedness #-}

-- The graded carry at the intended instance, and what it still owes layer 1.
--
-- `UC.Audit` proves the carry generically; all this instance has to supply is
-- the one-sided reading of its observation, which at `Dₚ` is `Pr≤` at a budget
-- (`massᴹ`).  What remains open is the other end: an audit-watching STRATEGY has
-- to be recognized as one of the ancilla contexts the graded bound quantifies
-- over, which is `UC.Seam`'s embedding one grade up.
--
-- The two together are the ledger example's path: `audit-carry` moves
-- `POVaudit` from the ideal system to the real one across an emulation, and
-- `Examples.ChimericLedger.POV.TrajectoryFromAudit` turns the audit bound back
-- into the trajectory statement `POV`.  That is the route `pov-carry` takes
-- through direct agreement, with the simulator kept instead of collapsed.

open import Data.Bool.Base using (true)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (proj₁)
open import Data.Rational using (ℚ)
open import Level using (Level; 0ℓ; suc; _⊔_)

open import ProbabilisticLogic.Dp.Advantage using (Pr≤)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.Protocol.Observe using (Bounded)
open import CategoricalCrypto.Strategy using (Strat)
open import CategoricalCrypto.UC.Approximate using (Mass)
open import CategoricalCrypto.Machines.Base using (𝒢ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Machine using (Proc; Observationᴹ; gradingᴹ; ucBaseᴹ)

import CategoricalCrypto.UC.Audit as Aud
import CategoricalCrypto.UC.Emulation as Em

-- The grading is no longer a parameter: `UC.Machine.gradingᴹ` is the only one
-- there is (its header prices why an `Iface`-object grading is not affordable).
module CategoricalCrypto.UC.Seam.Audit
  {qs : Level} (bud : Budget (𝒢ₚ 0ℓ) gradingᴹ qs) where

-- The reading `Observation` deliberately lacks: a mass at a budget, and the
-- ε-domination that `_≈ₚ[_]_`'s left half already is, read off the agreement at
-- the slack asked for.  `Mass` is one-sided — an audit bound is a probability of
-- an event — so it takes the `true` half of the two-sided domination.
massᴹ : Mass Observationᴹ
massᴹ = record { at = Pr≤ ; dominate = λ h δ δ>0 → proj₁ (h δ δ>0) true }

private
  module A = Aud ucBaseᴹ bud massᴹ
  module E = Em ucBaseᴹ

open A public using (_≤UC[_]_; sim; sim-qb; emulate; simCost; AuditBound; audit-carry)
open E using (_∘_)

------------------------------------------------------------------------
-- What layer 1 still needs

-- `𝟘 ⊗ᴵ B` rather than `𝟘 ⊛ B`: the grading's action at `⟦_⟧ᴵ`-images IS the
-- interface tensor, definitionally, so this is the same statement written in
-- the vocabulary layer 0 already has.
module TrivialGrade (𝟘 : Iface) (ι : (B : Iface) → Proc B (𝟘 ⊗ᴵ B)) where

  -- The consumer end of the graded bound: at the trivial grade an audit-watching
  -- strategy, embedded as an environment, IS one of the contexts `AuditBound`
  -- quantifies over, so the graded bound restricts to layer 1's own `Bounded`.
  -- Stated and priced at ~120–180 LOC on top of `Adequacy`: the test is
  -- `UC.Seam.strategyEnv B (bad d)` plugged through the wires that kill `𝟘` and
  -- the `unitᴵ` ancilla, its certificate is the strategy's own ask-depth
  -- (`Counting`, at `ctxBudget q 1 = q`), and reading its mass as `Pr` is
  -- `PrAgree` — the same two obligations `agree-to-adv` rests on, one grade up.
  AuditIsBounded : Set (suc 0ℓ ⊔ qs)
  AuditIsBounded = {B : Iface} (P : Protocol unitᴵ B)
                   (bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) (ε : ℕ → ℚ)
                 → AuditBound {⟦ unitᴵ ⟧ᴵ} {⟦ B ⟧ᴵ} {⟦ 𝟘 ⟧ᴵ} (ι B ∘ morphism P) ε
                 → Bounded P bad ε
