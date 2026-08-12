{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- Merkle–Damgård realizes a random oracle, in the UC sense.
--
-- `Examples.MerkleDamgard` proves the concrete, output-only statement: against
-- any adaptive ≤ q-query distinguisher, `MD ⊚ Comp.M` and a variable-length
-- random oracle differ by at most `bound q`.  That is exactly a
-- `OutputOnly.Realization`, so the whole UC argument is the general one:
-- ingestion into ℰᵗᵛ, ε-absorption, and the dummy-adversary theorem.  All this
-- module does is name the artifact, choose a SCHEDULE of security levels, and
-- read the conclusion back in Merkle–Damgård's own vocabulary.
--
-- The bound vanishes only for schedules whose hash width grows against the
-- query budget (e.g. `n j = j` with `k` polynomial), which is why `van` is a
-- hypothesis of the payoff rather than a theorem here.
--------------------------------------------------------------------------------

open import CategoricalCrypto.Interaction using (TraceDeterminesRun)
open import CategoricalCrypto.Machine.Probabilistic using (Machines)
import CategoricalCrypto.Machine.Probabilistic.Model as Machine
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E-Mono-On)

module CategoricalCrypto.Examples.MerkleDamgard.UC
  (PM : Machines) (MM : Machine.MachineModel PM) (E-mono-on : E-Mono-On) where

open import Data.Bool.Base using (Bool)
open import Data.Nat using (ℕ; NonZero)
open import Data.Vec.Base using (Vec)

open Machine PM
open MachineModel MM

open import CategoricalCrypto.Examples.MerkleDamgard PM trace-run E-mono-on
open import CategoricalCrypto.OutputOnly PM MM

-- The Merkle–Damgård artifact at one security level: the compression oracle as
-- the resource, MD as the protocol, the variable-length oracle as the ideal.
mdRealization : (n k : ℕ) ⦃ _ : NonZero k ⦄ (IV : Vec Bool n) → Realization
mdRealization n k IV = record
  { Res-If   = MD.Comp.Interface n k IV
  ; Ideal-If = MD.General.Interface n k IV
  ; resource = MD.Comp.M n k IV
  ; protocol = MD.MD n k IV
  ; ideal    = MD.General.M n k IV
  ; bound    = MD.bound n k IV
  ; secure   = MD.indistinguishable n k IV
  }

-- A schedule assigns each security level its hash width and block count.
module AtSchedule (n k : ℕ → ℕ) (k≢0 : ∀ j → NonZero (k j)) (IV : ∀ j → Vec Bool (n j)) where

  mdRealizations : ℕ → Realization
  mdRealizations j = mdRealization (n j) (k j) ⦃ k≢0 j ⦄ (IV j)

  open Ingest mdRealizations public

  module Theorem
    (qbComp : FC.PolyQB resFam)
    (qbMD   : FC.PolyQB protoFam)
    (qbGen  : FC.PolyQB idealFam)
    (reflects : Reflects)
    (van : VT.VanishingBound A.bound)
    where

    open Payoff qbComp qbMD qbGen reflects van public

    -- `real` is `MD ⊚ Comp.M` conjugated into the degenerate grade and `Ideal`
    -- is the variable-length random oracle, so this IS Merkle–Damgård's claim.
    MD≤UC-ROᵗᵛ : real ST.≤UC Ideal
    MD≤UC-ROᵗᵛ = realizes
