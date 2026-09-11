{-# OPTIONS --safe --without-K --guardedness #-}

-- Runs that reach a verdict.
--
-- `TotalRun M` says every strategy plays `M` to a verdict: the two verdict
-- masses are at one already at a finite budget.  It is the anchor the seam's
-- collapse needs — a cofinal domination compares SHAPES of `cum` families and
-- nothing in it pins the scale, so "the simulator does not lose mass" can only
-- be read off against a side whose mass is known (`Dp.Mass.squeeze`).
--
-- For a protocol image the budget half is free: `PrAgree` already says the
-- machine run's verdict mass is layer 1's own `Prᵇ` past a budget, so what is
-- left is the layer-1 liveness `Pr true + Pr false ≡ 1ℚ` — genuinely a side
-- condition, `Protocol.Observe.evalC` sending a `dead` call tree to `nothing`.
-- `totalRun-resp-≈ᴹ` and `totalRun-∘` then carry it along the machine equality
-- and through `Morphism-∘`, so a composite of protocol images discharges it by
-- name.

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 1ℚ)
open import Data.Rational.Properties using (≤-trans; ≤-reflexive)
open import Data.Sum.Base using (_⊎_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst; cong₂)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (Pr≤[_])
open import ProbabilisticLogic.Dp.Mass using (Total; total-resp-≼ₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒢ₚ; 𝒫ₚ)
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Agree using (prAgree)
open import CategoricalCrypto.Protocol.Machine.Compose using (morphism-∘)
open import CategoricalCrypto.Protocol.Observe using (Prᵇ)
open import CategoricalCrypto.Strategy using (Strat)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Protocol.Machine.Total where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝒢  = Category (𝒢ₚ 0ℓ)

-- Spelled at the closed-machine shape `Protocol.Machine.runᴹ` is typed at,
-- which is `UC.Machine.Proc unitᴵ B` one layer up.
TotalRun : (B : Iface) → MC.Machine (⊥ ⊎ Neg B) (⊥ ⊎ Pos B) → Set
TotalRun B M = (d : Strat (Neg B) (Pos B)) → Total (runᴹ M d)

totalRun-resp-≈ᴹ : (B : Iface) (u v : MC.Machine (⊥ ⊎ Neg B) (⊥ ⊎ Pos B))
                 → u S.≈ᴹ v → TotalRun B u → TotalRun B v
totalRun-resp-≈ᴹ B u v e t d =
  total-resp-≼ₚ (runᴹ u d) (runᴹ v d) (proj₁ (runᴹ-resp-≈ᴹ e d)) (t d)

module _ (B : Iface) (P : Protocol unitᴵ B) where

  private
    x : Strat (Neg B) (Pos B) → Dₚ Bool
    x = runᴹ (morphism P)

  -- Both verdict masses are read off at one budget: each `PrAgree` witness
  -- tolerates any excess, so their sum serves for both.
  totalRun-morphism : ((d : Strat (Neg B) (Pos B)) → 1ℚ ℚ.≤ Prᵇ P true d ℚ.+ Prᵇ P false d)
                    → TotalRun B (morphism P)
  totalRun-morphism live d = nt + nf , ≤-trans (live d) (≤-reflexive (sym reads))
    where
    nt = proj₁ (prAgree true  P d)
    nf = proj₁ (prAgree false P d)

    reads : Pr≤[ true ] (nt + nf) (x d) ℚ.+ Pr≤[ false ] (nt + nf) (x d)
          ≡ Prᵇ P true d ℚ.+ Prᵇ P false d
    reads = cong₂ ℚ._+_ (proj₂ (prAgree true P d) nf)
                        (subst (λ k → Pr≤[ false ] k (x d) ≡ Prᵇ P false d) (+-comm nf nt)
                               (proj₂ (prAgree false P d) nt))

------------------------------------------------------------------------
-- …and through a composite

-- Every polarity is passed explicitly, for `UC.QueryBound`'s reason: left to
-- inference, each asks Agda to invert `Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)` for the
-- pair, and `_⊎_` is not a constructor.
morphismCompose : Morphism-∘
morphismCompose {A} {B} {C} P₂ P₁ =
  morphism-∘ P₂ P₁ S.○ᴹ
  Col.compose-raw≈∘ᴳ {Pos A} {Neg A} {Pos B} {Neg B} {Pos C} {Neg C}
                     (morphism P₂) (morphism P₁)

totalRun-∘ : (B C : Iface) (P₂ : Protocol B C) (P₁ : Protocol unitᴵ B)
           → TotalRun C (morphism (P₂ ∘ᵖ P₁))
           → TotalRun C (morphism P₂ 𝒢.∘ morphism P₁)
totalRun-∘ B C P₂ P₁ =
  totalRun-resp-≈ᴹ C (morphism (P₂ ∘ᵖ P₁))
    (𝒢._∘_ {⟦ unitᴵ ⟧ᴵ} {⟦ B ⟧ᴵ} {⟦ C ⟧ᴵ} (morphism P₂) (morphism P₁))
    (morphismCompose P₂ P₁)
