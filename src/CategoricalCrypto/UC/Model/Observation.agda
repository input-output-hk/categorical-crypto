{-# OPTIONS --safe --without-K --guardedness #-}

-- The verdict object and what a closed process shows at it (proposal §1–2,
-- `docs/kb/frontier/15-probabilistic-uc-model.typ`).
--
-- `Ωᵒ` is TICKED, for `UC.Machine.Ωᴵ`'s reason: a machine is reactive, so a
-- verdict interface with an empty negative side could never be activated and
-- would observe nothing.  The tick is the environment's single activation and
-- `Obs` is the one-ask closed run at it.
--
-- The identification of observations is TWO-SIDED and comes ready-made:
-- `_≈ₚ[_]_` compares BOTH verdict masses (`Dp.Advantage`'s header — the
-- `true`-mass alone would identify answering `false` with diverging), and
-- `Approximation._∼ᵃ_` closes it under every positive slack, which is the
-- equivalence `UC.Approximate.Induced` already builds an `Observation` out of.
--
-- Closures are taken at `𝟘ᵒ = ifaceᵒ unitᴵ` rather than at the seal's monoidal
-- unit.  Both objects are the empty interface — the unit is the base's
-- polymorphic `⊥` in both polarities — so they carry the same closures and cut
-- the same quotient, and `𝟘ᵒ` is the one the machine layer's closed run is
-- already typed at (`UC.Machine.Run.Closed`).

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Bool.Base using (Bool)
open import Data.Rational.Properties using (<⇒≤)
open import Data.Unit.Base using (tt)
open import Level using (0ℓ; suc)
open import Relation.Binary.Structures using (IsEquivalence)

open import ProbabilisticLogic.Dp using (Dₚ; _≈ₚ_)
open import ProbabilisticLogic.Dp.Advantage using (≈ₚ⇒≈ₚ[0]; ≈ₚ[]-mono; ≈ₚ[]-resp)

open import CategoricalCrypto.Iface using (unitᴵ)
open import CategoricalCrypto.Strategy using (ask; out)
open import CategoricalCrypto.UC.Approximate using (Approximation)
open import CategoricalCrypto.UC.Machine using (Approximationᴹ; Ωᴵ; ⟦_⟧ᴼ)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)
open import CategoricalCrypto.UC.Model.Seal

module CategoricalCrypto.UC.Model.Observation where

private
  module Ap = Approximation Approximationᴹ
  module G = MonoidalCategory 𝔾ᵒ

Ωᵒ 𝟘ᵒ : G.Obj
Ωᵒ = ifaceᵒ Ωᴵ
𝟘ᵒ = ifaceᵒ unitᴵ

Test Closure : G.Obj → Set (suc 0ℓ)
Test X = X G.⇒ Ωᵒ
Closure X = 𝟘ᵒ G.⇒ X

Obs : Closure Ωᵒ → Dₚ Bool
Obs u = ⟦ unprocᵒ u ⟧ᴼ

infix 4 _∼ᴼ_

_∼ᴼ_ : Dₚ Bool → Dₚ Bool → Set
_∼ᴼ_ = Ap._∼ᵃ_

∼ᴼ-isEquivalence : IsEquivalence _∼ᴼ_
∼ᴼ-isEquivalence = Ap.∼ᵃ-isEquivalence

≈ₚ⇒∼ᴼ : {d e : Dₚ Bool} → d ≈ₚ e → d ∼ᴼ e
≈ₚ⇒∼ᴼ eq _ pos = ≈ₚ[]-mono (<⇒≤ pos) (≈ₚ⇒≈ₚ[0] eq)

∼ᴼ-resp : {d d′ e e′ : Dₚ Bool} → d ≈ₚ d′ → e ≈ₚ e′ → d ∼ᴼ e → d′ ∼ᴼ e′
∼ᴼ-resp p q h ε pos = ≈ₚ[]-resp p q (h ε pos)

-- A simulation is invisible to a closed run (`UC.Machine.Run`), so the seal's
-- hom equality is observed EXACTLY, not merely up to every positive slack.
obs-resp : {u v : Closure Ωᵒ} → u G.≈ v → Obs u ≈ₚ Obs v
obs-resp e = runᴹ-resp-≈ᴹ (≈ᵒ⇒≈ᴹ e) (ask tt out)
