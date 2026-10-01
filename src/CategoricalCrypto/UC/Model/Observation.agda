{-# OPTIONS --safe --without-K --guardedness #-}

-- The verdict object and what a closed process shows at it.
--
-- `Ωᵒ` is TICKED, for `UC.Machine.Ωᴵ`'s reason: a machine is reactive, so a
-- verdict interface with an empty negative side could never be activated and
-- would observe nothing.  The tick is the environment's single activation and
-- `Obs` is the one-ask closed run at it.
--
-- The identification of observations is TWO-SIDED and comes ready-made:
-- `_≈ₚ[_]_` compares BOTH verdict masses (`Dp.Advantage`'s header — the
-- `true`-mass alone would identify answering `false` with diverging), and
-- `AllPositive._∼ᵃ_` closes it under every positive slack.
--
-- Closures are taken at `𝟘ᵒ = ifaceᵒ unitᴵ` rather than at the seal's monoidal
-- unit.  Both objects are the empty interface, differing only in which empty
-- type spells each polarity — `Data.Empty.⊥` against the base's polymorphic
-- one — and `𝟘ᵒ` is the spelling the machine layer's closed run is already
-- typed at (`Protocol.Machine.Closed`), which is what lets that run and its
-- simulation-invariance be reused unchanged.  The two are not identified: the
-- metatheorems are ℰ-generic and never see the closure object, and the iso
-- costs >150 s (`docs/stduc-supersession-plan.md` §1.1).

open import Categories.Category.Monoidal.Bundle

open import Data.Bool.Base
open import Data.Unit.Base
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Core
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Model.Seal

module CategoricalCrypto.UC.Model.Observation where

private
  module Ap = AllPositive ℚ-refinement Approximationᴹ
  module G = MonoidalCategory 𝔾ᵒ

Ωᵒ 𝟘ᵒ : G.Obj
Ωᵒ = ifaceᵒ Ωᴵ
𝟘ᵒ = ifaceᵒ unitᴵ

Obs : 𝟘ᵒ G.⇒ Ωᵒ → Dₚ Bool
Obs u = ⟦ unprocᵒ u ⟧ᴼ

∼ᴼ-resp : {d d′ e e′ : Dₚ Bool} → d ≈ₚ d′ → e ≈ₚ e′ → d Ap.∼ᵃ e → d′ Ap.∼ᵃ e′
∼ᴼ-resp p q h ε pos = ≈ₚ[]-resp p q (h ε pos)

-- A simulation is invisible to a closed run (`UC.Machine.Run`), so the seal's
-- hom equality is observed EXACTLY, not merely up to every positive slack.
obs-resp : {u v : 𝟘ᵒ G.⇒ Ωᵒ} → u G.≈ v → Obs u ≈ₚ Obs v
obs-resp e = runᴹ-resp-≈ᴹ (≈ᵒ⇒≈ᴹ e) (ask tt out)

------------------------------------------------------------------------
-- …as the records the layers above ask for

-- The QUANTITATIVE readout is primary and the qualitative one is `qual₊` of
-- it, so `UC.Model.Family` gets its error structure from the very space
-- `Ap._∼ᵃ_` collapses instead of a second, parallel record.
qevaluationᵒ : QEvaluation ∣𝔾ᵒ∣ 0ℓ 0ℓ
qevaluationᵒ = record
  { J = 𝟘ᵒ ; Ω = Ωᵒ ; X = spaceᴹ
  ; eval₀ = record { to = Obs ; cong = λ e → ≈ₚ⇒≈ₚ[0] (obs-resp e) }
  }

evaluationᵒ : Evaluation ∣𝔾ᵒ∣ 0ℓ 0ℓ
evaluationᵒ = qual₊ ℚ-refinement qevaluationᵒ
