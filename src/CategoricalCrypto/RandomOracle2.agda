{-# OPTIONS --safe #-}

-- §3 of the plan (M5/M6) over the naive locally graded layer: the random
-- oracle, end to end, derived from the Abstract2 §1 metatheory against the
-- Merkle–Damgård artifact of `Examples.MerkleDamgardUC`.  Protocols are bare
-- machine morphisms: the real protocol IS the composite `MD-mach ∘ Comp-M`,
-- because `T₀ Jre GenIf` reduces to `Jre ⊗ GenIf` under the curriedTensor
-- triple.  The two bridges the ≈ᵁ formulation needs are both DERIVED here:
--   • M5, ε-absorption — a concrete per-budget bound with a vanishing profile
--     establishes the kernel equality of ℰᵗᵛ (`VanishingTV.absorb`);
--   • M6, the ideal protocol and its simulator — at the degenerate grade
--     `Jre = Kid = 𝟙^ω` the simulator is the identity and the bridge is the
--     graded unit law `sub id ∘ g ≈ g` (`sub-identityˡ`), so `roIdeal` is
--     `General-M` itself.
-- `GradeStable`, once an honest hypothesis here, is Track A's `grade-stableᵗᵛ`.
-- What remains open is exactly `MDAssumptions` plus `MachineHyp`, `hom-triv`,
-- `Reflects`, the three `PolyQB` witnesses and `van` — all module parameters.

open import CategoricalCrypto.Examples.MerkleDamgard.Base using (MDAssumptions)

module CategoricalCrypto.RandomOracle2 (mdAssumptions : MDAssumptions) where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (_,_)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import CategoricalCrypto.Examples.MerkleDamgardUC mdAssumptions
open import CategoricalCrypto.MachineAxioms using (MachineAxioms)

module MDisRO
  (mh : MachineHyp)
  (hom-triv : MachineAxioms.HomTransportTrivial (MachineHyp.axioms mh))
  (art : ℕ → ROArtifact)
  where
  open AtUnitGrade mh hom-triv art

  -- ── THE PAYOFF, DERIVED ───────────────────────────────────────────────────
  module Payoff
    (qbComp : FC.PolyQB compFam)
    (qbMD   : FC.PolyQB mdFam)
    (qbGen  : FC.PolyQB genFam)
    (reflects : Reflects)
    (van : VT.VanishingBound A.bnd)
    where
    open Assemble qbComp qbMD qbGen reflects van

    -- The real protocol is the MD composite itself — a bare machine morphism at
    -- grade 𝟙^ω.
    mdProtocol : Ao FC.⇒^ω ST.T₀ FC.𝟙^ω GenIf
    mdProtocol = MD-mach Cω.∘ Comp-M

    -- M6 at the degenerate grade.  Both `sub`'s object implicit and the grade
    -- are read off `roIdeal`'s ascribed type, which is why it is named.
    roIdeal : Ao FC.⇒^ω ST.T₀ FC.𝟙^ω GenIf
    roIdeal = General-M

    roSimulator : FC.𝟙^ω FC.⇒^ω FC.𝟙^ω
    roSimulator = Cω.id

    ideal-bridge : (ST.sub roSimulator Cω.∘ roIdeal) ST.≈ℰ General-M
    ideal-bridge = ST.≈C⇒≈ℰ (ST.sub-identityˡ General-M)

    -- Consumes only the ε-absorption of the MD artifact (`MD-secure` + `van`)
    -- and `ideal-bridge`.  `ε` must be pinned: it occurs applied (`ε n (p n)`)
    -- inside `≈ℰ[_]`, so inferring it strands a non-pattern constraint.
    md-emulate : mdProtocol ST.≈ℰ (ST.sub roSimulator Cω.∘ roIdeal)
    md-emulate = begin
        mdProtocol                       ≈⟨ VT.absorb {ε = A.bnd} MD-secure van ⟨
        General-M                        ≈⟨ ideal-bridge ⟨
        ST.sub roSimulator Cω.∘ roIdeal  ∎
      where open SetoidR (ST.≈ℰ-setoid Ao Bo)

    MD≤UC-ROᵗᵛ : mdProtocol ST.≤UC roIdeal
    MD≤UC-ROᵗᵛ = ST.dummy-complete (roSimulator , ST.bridge ST.grade-stableᵗᵛ md-emulate)
