{-# OPTIONS --safe --without-K --guardedness #-}

-- The links of the seam that need the grading: an ℰ-agreement, whose ancilla
-- quantifier ranges over abstract contexts, is seen by the concrete
-- environments `UC.Seam.strategyEnv` builds — and an emulation at the TRIVIAL
-- grade is such an agreement, so `pov-carry`'s premise follows from `_≤UC_`
-- there.
--
-- The metatheory is the INHERITED one, read at the sealed machine bundle
-- (`UC.Model.Setup`).  Which of its relations each statement is read in is
-- forced, and getting it wrong silently weakens: the seam's agreements carry an
-- ancilla quantifier, so at a GRADED codomain they are `_≈ᵁ_` and at an
-- ungraded one `UC.Core.Bridge._≈ᴳ_` — never StdUC's bare `_≈ℰ_`, which has no
-- ancilla in it (`docs/stduc-supersession-plan.md`, finding F1).  `_≈ᴳ_` is the
-- core's relation exactly (`≈ᴳ⇔≈ℰᶜ`), so nothing below says less than it did.
--
-- Grades and ancillas are objects of the SEAL rather than `Iface`s, and the
-- ancilla quantifier of an agreement ranges over every one of them:
-- restricting the witnesses to `ifaceᵒ`-images would be a weakening that the
-- transparent spelling — where `retᴵ` inverts `⟦_⟧ᴵ` definitionally — did not
-- have.  That inverse is exported under the seal as well
-- (`UC.Model.Seal.objᵒ`), so a statement written at `Iface` can be READ at
-- every object instead of being restricted to the images
-- (`UC.Model.Dominated`); nothing below needs that reading.
--
-- Everything below is a STATEMENT, and that is measured rather than chosen: at
-- this instance a term whose type is an agreement between machine COMPOSITES
-- exhausts a 3 GiB heap even for the identity application `h u v e = h u v e`,
-- because the relation unfolds through the observation's projections and
-- η-expands `Observationᴹ`, whose `⟦⟧-resp-≈` drags the machine equality in with
-- it — the same reason `UC.Seam.Agreeˢ` is spelled in the `Dₚ` vocabulary.  So
-- the reasoning that composes these statements is proved once and generically
-- (`UC.Core.Bridge.≈ᴳ-at` for the grounding below, `ProbabilisticLogic.Dp.Mass`
-- for the collapse's ε-arithmetic, `UC.Audit.audit-carry` for the graded
-- carry), and this module only names what the instance still owes.

open import ProbabilisticLogic.Dp.Mass using (ASTotal)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine.Total using (TotalRun)
open import CategoricalCrypto.Strategy using (Strat)
open import CategoricalCrypto.UC.Machine using (Proc; Ωᴵ)
open import CategoricalCrypto.UC.Model.Observation using (Closure; Obs; Test; Ωᵒ; 𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (ifaceᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam using (Agreeˢ; strategyEnv)

module CategoricalCrypto.UC.Seam.Grounding where

StratIsEnv : Set₁
StratIsEnv = (B : Iface) (u v : Proc unitᴵ B) → procᵒ u ≈ᴳ procᵒ v → Agreeˢ B u v

opaque
  Proc≈ : (A B : Iface) → ifaceᵒ A ⇒ ifaceᵒ B → ifaceᵒ A ⇒ ifaceᵒ B → Set₁
  Proc≈ A B u v = u ≈ v

opaque
  unfolding Proc≈

  toProc≈ : {A B : Iface} {u v : ifaceᵒ A ⇒ ifaceᵒ B} → u ≈ v → Proc≈ A B u v
  toProc≈ p = p

  fromProc≈ : {A B : Iface} {u v : ifaceᵒ A ⇒ ifaceᵒ B} → Proc≈ A B u v → u ≈ v
  fromProc≈ p = p

-- What `StratIsEnv` reduces to: an embedded strategy PRESENTED as one of the
-- ancilla contexts an agreement quantifies over.  Its four fields are exactly
-- `UC.Core.Bridge.≈ᴳ-at`'s arguments at `k = strategyEnv B d ∘_`, which is
-- where the reduction is proved and where the ε-arithmetic and the transport of
-- both endpoints are spent — generically, so that nothing about the machines
-- unfolds.  The obligation left here is one equation and no quantitative
-- content at all.
opaque
  EnvPlugs : (B : Iface) (d : Strat (Neg B) (Pos B)) (anc : Channel)
           → Test (T₀ anc (ifaceᵒ B)) → Closure (T₀ anc 𝟘ᵒ) → Set₁
  EnvPlugs B d anc test close = (w : 𝟘ᵒ ⇒ ifaceᵒ B)
    → Proc≈ unitᴵ Ωᴵ ((test ∘ T₁ anc w) ∘ close) (procᵒ (strategyEnv B d) ∘ w)

opaque
  unfolding EnvPlugs

  toEnvPlugs : {B : Iface} {d : Strat (Neg B) (Pos B)} {anc : Channel}
               {test : Test (T₀ anc (ifaceᵒ B))} {close : Closure (T₀ anc 𝟘ᵒ)}
             → ((w : 𝟘ᵒ ⇒ ifaceᵒ B) → Proc≈ unitᴵ Ωᴵ
                 ((test ∘ T₁ anc w) ∘ close) (procᵒ (strategyEnv B d) ∘ w))
             → EnvPlugs B d anc test close
  toEnvPlugs p = p

  fromEnvPlugs : {B : Iface} {d : Strat (Neg B) (Pos B)} {anc : Channel}
                 {test : Test (T₀ anc (ifaceᵒ B))} {close : Closure (T₀ anc 𝟘ᵒ)}
               → EnvPlugs B d anc test close
               → (w : 𝟘ᵒ ⇒ ifaceᵒ B) → Proc≈ unitᴵ Ωᴵ
                   ((test ∘ T₁ anc w) ∘ close) (procᵒ (strategyEnv B d) ∘ w)
  fromEnvPlugs p = p

record EnvCtx (B : Iface) (d : Strat (Neg B) (Pos B)) : Set₁ where
  field
    anc   : Channel
    test  : Test (T₀ anc (ifaceᵒ B))
    close : Closure (T₀ anc 𝟘ᵒ)
    plugs : EnvPlugs B d anc test close

-- At the unit ancilla the witnesses are `test = strategyEnv B d ∘ λ⇒`, the
-- closure `λ⇐`, and `plugs` the cancellation of `T₁ unit` against the two
-- wires: the unitor's naturality and its own iso, two fields of the monoidal
-- record (`UC.Seam.Grounded`).  The gotcha is the grade `unitᴵ`, which is NOT
-- the bundle's unit — no `T₁ Y w ≈ w` is derivable at it, and the equation
-- falls through to the ⊕-trace.
EnvAsCtx : Set₁
EnvAsCtx = (B : Iface) (d : Strat (Neg B) (Pos B)) → EnvCtx B d

-- `EnvAsCtx → StratIsEnv` is then the one-line application of `≈ᴳ-at` to those
-- four fields.  At the transparent grading it was measured BLOCKED, twice — at
-- 300 s and an 8 GiB heap in four spellings (`∼-cast` inline; `≈ℰ-at` with both
-- object implicits passed; `Dp.Advantage.≈ₚ[]-resp` against an
-- observation-level `plugs`; the same with the three components as module
-- parameters rather than record fields), then re-measured at 2400 s — and what
-- was left after excluding the transport, the bundling and the implicits was
-- the instance's own unfolding under the application.  Under the seal the
-- application is at the startup floor: the conversion has nothing to unfold.

------------------------------------------------------------------------
-- The trivial grade

-- The degenerate end of the grading: a grade object that can carry no message,
-- and the wire that inflates a closed process to it.  At the intended instance
-- both are the bundle's own (`𝟘 = unit`, `ι = unitorˡ.to`).  Both are module
-- PARAMETERS rather than fields of a record bundling them, which is the
-- medicine `UC.QueryBound.Certified` takes for the same cliff: a use site
-- supplies them where the conversion is a plain application.
module TrivialGrade (𝟘 : Channel) (ι : (B : Iface) → ifaceᵒ B ⇒ T₀ 𝟘 (ifaceᵒ B)) where

  -- A simulator on the trivial grade never fires: its interface is empty.  The
  -- one thing it can still do to an observation is SCALE it, by the
  -- termination mass of its own initialization — that is what
  -- `UC.Seam.Grounding.Dead` propagates (at mass 0; the general statement is
  -- the same argument) and it is why blindness needs a hypothesis at all: at
  -- mass 0 a simulator makes every ideal invisible.
  --
  -- `SimTotal` is that hypothesis, read where the seal lets it be read.  The
  -- scalar's point is not nameable here — under the seal a hom exposes no
  -- machine — so the mass is read off the simulated ideal instead, at the
  -- embedded strategies, through a test that deflates the grade to one (`𝟘` is
  -- a parameter here; its unitor is next door, `UC.Seam.Grounded`).  Almost
  -- sure rather than exact: a cofinal domination cannot say more, and an
  -- ε-closed agreement needs no more.
  SimTotal : (B : Iface) → 𝟘 ⇒ 𝟘 → Proc unitᴵ B → Set₁
  SimTotal B s v = (d : Strat (Neg B) (Pos B)) (t : T₀ 𝟘 (ifaceᵒ B) ⇒ Ωᵒ)
                 → Proc≈ B Ωᴵ (t ∘ ι B) (procᵒ (strategyEnv B d))
                 → ASTotal (Obs (t ∘ (sub s ∘ (ι B ∘ procᵒ v))))

  SubBlind : Set₁
  SubBlind = (B : Iface) (s : 𝟘 ⇒ 𝟘) (v : Proc unitᴵ B) → SimTotal B s v
           → sub s ∘ (ι B ∘ procᵒ v) ≈ᵁ ι B ∘ procᵒ v

  -- …and so is the wire itself, in the direction grade stability does not give:
  -- the ancilla quantifier at `W ⊗₀ (𝟘 ⊗₀ B)` reaches every context at
  -- `W ⊗₀ B`, `𝟘` contributing nothing.
  IotaBlind : Set₁
  IotaBlind = (B : Iface) (u v : Proc unitᴵ B)
            → ι B ∘ procᵒ u ≈ᵁ ι B ∘ procᵒ v → procᵒ u ≈ᴳ procᵒ v

  -- The unit-grade specialization: at the trivial grade an emulation IS the
  -- direct agreement `pov-carry` consumes.  The consumer assumes literally
  -- `u ≤UC v`; what it assumes BESIDES is about the two machines and not about
  -- the simulator, which is the point — `Protocol.Machine.Total` discharges
  -- `TotalRun` by name for a protocol image and for a composite of two.
  --
  -- Totality is not decoration: with `u` divergent, EVERY `v` is emulated (the
  -- simulator that never starts makes the ideal invisible) while `Agreeˢ` still
  -- compares the runs.  It is also exactly what the collapse spends — the
  -- squeeze reads the simulator's mass off `u`'s own (`UC.Seam.Grounded`).
  UnitGrade : Set₁
  UnitGrade = (B : Iface) (u v : Proc unitᴵ B) → TotalRun B u → TotalRun B v
            → ι B ∘ procᵒ u ≤UC ι B ∘ procᵒ v → Agreeˢ B u v
