{-# OPTIONS --safe --without-K --guardedness #-}

-- What the trivial-grade collapse owes, stated: `SimTotal`, that the
-- simulator's own initialization terminates almost surely, and `SubBlind`,
-- that such a simulator is then invisible.  `UC.Seam.Grounded` discharges both.
--
-- The metatheory is the INHERITED one, read at the sealed machine bundle
-- (`UC.Model.Setup`).  Which of its relations each statement is read in is
-- forced, and getting it wrong silently weakens: the seam's agreements carry an
-- ancilla quantifier, so at a GRADED codomain they are `_≈ᵁ_` — never StdUC's
-- bare `_≈ℰ_`, which has no ancilla in it (`docs/stduc-supersession-plan.md`,
-- finding F1).
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
-- η-expands `Observationᴹ`, whose `⟦⟧-resp-≈` drags the machine equality in
-- with it.  So the reasoning that composes these statements is proved once and
-- generically (`UC.Core.Bridge.≈ᴳ-at` for the grounding, `Dp.Mass` for the
-- collapse's ε-arithmetic), and this module only names what the instance owes.

open import ProbabilisticLogic.Dp.Mass using (ASTotal)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Strategy using (Strat)
open import CategoricalCrypto.UC.Machine using (Proc; Ωᴵ)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ)
open import CategoricalCrypto.UC.Model.Seal using (ifaceᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam using (strategyEnv)

module CategoricalCrypto.UC.Seam.Grounding where

opaque
  Proc≈ : (A B : Iface) → ifaceᵒ A ⇒ ifaceᵒ B → ifaceᵒ A ⇒ ifaceᵒ B → Set₁
  Proc≈ A B u v = u ≈ v

opaque
  unfolding Proc≈

  toProc≈ : {A B : Iface} {u v : ifaceᵒ A ⇒ ifaceᵒ B} → u ≈ v → Proc≈ A B u v
  toProc≈ p = p

  fromProc≈ : {A B : Iface} {u v : ifaceᵒ A ⇒ ifaceᵒ B} → Proc≈ A B u v → u ≈ v
  fromProc≈ p = p

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
