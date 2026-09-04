{-# OPTIONS --safe --without-K --guardedness #-}

-- The links of the seam that need the grading: an ℰ-agreement, whose ancilla
-- quantifier ranges over abstract contexts, is seen by the concrete
-- environments `UC.Seam.strategyEnv` builds — and an emulation at the TRIVIAL
-- grade is such an agreement, so `pov-carry`'s premise follows from `_≤UC_`
-- there.
--
-- They live here rather than in `UC.Seam` because instantiating the environment
-- layer at a `Grading 𝒫ᴵ` costs a heap budget of the same order as the seam's
-- own machine conversions, and nothing else in the seam needs it — the carry
-- (`agree-to-adv`, `pov-carry`) runs on `Agreeˢ` alone.
--
-- Everything below is a STATEMENT, and that is measured rather than chosen: at
-- this instance a term whose type is an `≈ℰ` between machine COMPOSITES exhausts
-- a 3 GiB heap even for the identity application `h u v e = h u v e`, because
-- `≈ℰ` unfolds through the observation's projections and η-expands
-- `Observationᴹ`, whose `⟦⟧-resp-≈` drags the machine equality in with it — the
-- same reason `UC.Seam.Agreeˢ` is spelled in the `Dₚ` vocabulary.  So the
-- reasoning that composes these statements is proved once and generically
-- (`UC.Emulation.unit-grade` for the collapse below, `UC.Audit.audit-carry` for
-- the graded carry), and this module only names what the instance still owes.

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Core using (Grading)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; UCBaseᴹ)
open import CategoricalCrypto.UC.Seam using (Agreeˢ)

import CategoricalCrypto.UC.Emulation as Em

module CategoricalCrypto.UC.Seam.Grounding (G : Grading 𝒫ᴵ) where

private module E = Em (UCBaseᴹ G)

open E using (_∘_; _⊛_; sub; _≈ℰ_; _≤UC_)

-- Stated and priced at ~80–120 LOC: instantiate `_≈ℰ_` at `Y = unitᴵ`, at the
-- test `strategyEnv B d ∘ λᴵ⇒` and at the closure `λᴵ⇐ ∘ u`, and cancel
-- `T₁ᴵ unitᴵ` against the two wires.  The `unitᴵ` summands can never fire
-- (`⊥-unique`), so the cancellation holds; but it is an equation between
-- `𝒫ᴵ`-composites, hence between ⊕-traces, and so needs the trace fusion M2's
-- task 3 left open — the same gate as `Grading 𝒫ᴵ` itself.
StratIsEnv : Set₁
StratIsEnv = (B : Iface) (u v : Proc unitᴵ B) → u ≈ℰ v → Agreeˢ B u v

------------------------------------------------------------------------
-- The trivial grade

-- The degenerate end of the grading: a grade object that can carry no message,
-- and the wire that inflates a closed process to it.  At the intended instance
-- `𝟘 = unitᴵ` and `ι = UC.Machine.Bridge.λᴵ⇐`, where `ι B ∘ u` is `conjᴵ u`.  Both are
-- module PARAMETERS rather than fields of a record bundling them, which is the
-- medicine `UC.QueryBound.Certified` takes for the same cliff: a use site
-- supplies them where the conversion is a plain application.
module TrivialGrade (𝟘 : Iface) (ι : (B : Iface) → Proc B (𝟘 ⊛ B)) where

  -- A simulator on the trivial grade is invisible: its interface never fires,
  -- so no environment reads it.  Priced at ~60–90 LOC (the dead summand by
  -- `⊥-unique`) behind the same trace fusion as `StratIsEnv` — it is again an
  -- equation between `𝒫ᴵ`-composites.
  SubBlind : Set₁
  SubBlind = (B : Iface) (s : Proc 𝟘 𝟘) (v : Proc unitᴵ B)
           → (sub {𝟘} {𝟘} {B} s ∘ (ι B ∘ v)) ≈ℰ (ι B ∘ v)

  -- …and so is the wire itself, in the direction `grade-stable` does not give:
  -- the ancilla quantifier at `W ⊛ (𝟘 ⊛ B)` reaches every context at `W ⊛ B`,
  -- `𝟘` contributing nothing.  Same price and same gate.
  IotaBlind : Set₁
  IotaBlind = (B : Iface) (u v : Proc unitᴵ B)
            → (ι B ∘ u) ≈ℰ (ι B ∘ v) → u ≈ℰ v

  -- The unit-grade specialization: at the trivial grade an emulation IS the
  -- direct agreement `pov-carry` consumes.  The reduction is PROVED, generically
  -- and once, as `UC.Emulation.unit-grade` — the simulator collapses by
  -- `SubBlind`, the wire by `IotaBlind`, two lines — so what this instance owes
  -- is those two degeneracy facts plus `StratIsEnv`, and the closing application
  -- of them is what the header measures at a 3 GiB heap.
  UnitGrade : Set₁
  UnitGrade = (B : Iface) (u v : Proc unitᴵ B)
            → _≤UC_ {unitᴵ} {B} {𝟘} {𝟘} (ι B ∘ u) (ι B ∘ v) → Agreeˢ B u v
