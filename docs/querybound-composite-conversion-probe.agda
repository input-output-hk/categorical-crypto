{-# OPTIONS --safe --without-K --guardedness #-}

-- PROBE MODULE.  It lives in `docs/` and not under `src/` on purpose: the
-- library is `include: src`, so anything there is on every build, and this one
-- `refl` costs 421 s.  To run it, copy to
-- `src/CategoricalCrypto/UC/QueryBound/Compose/StepP.agda`, check it, delete it
-- again.  It exists to price, in isolation, the conversion
-- `𝒫._∘_ g f ≟ traceᴹ … (W.α ∘ᴹ ((g ⊗ᵉ f) ∘ᴹ W.γ))` — projecting `_∘_` out of
-- `𝒢ₚ`'s G-construction record and matching it against the hand-spelled
-- composite, which is what `Compose.Step`'s `qbᵢ-∘` and `Seam.Adequacy.
-- Wiring`'s `compose-≈ᴹ` each pay once.
--
-- MEASURED (warm, single module, `-M8G -H1G`, `--profile=definitions`):
-- total 429 s, of which `∘-computed` alone is 421 s.  That is 84% of `qbᵢ-∘`'s
-- 498 s and 54% of `Compose.Step`'s whole 780 s in the same session, so it is
-- the floor any restructuring of that module has to beat: the cost is one
-- conversion, not a sum of many, and it cannot be split.
--
-- Re-run this after any attempt on the defect; if the number has not moved,
-- neither has the problem.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.GConstructionTrace as GT

open import Data.Sum.Base using (_⊎_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
  using (𝒱ₚ; distₚ; 𝒫ₚ; Elgotₚ; Tracedₚ)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ)

import CategoricalCrypto.Machines.Bundle as Bundle
import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Trace as Trace

module CategoricalCrypto.UC.QueryBound.Compose.StepP where

private
  module 𝒫 = Category 𝒫ᴵ

module MB = Bundle (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)
module MK = MCat (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

open Core (𝒱ₚ 0ℓ)
open Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)
open Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)

private
  module W = GT MK.Mealy-Category MB.Mealy-Monoidal (Tracedₚ 0ℓ)

∘-computed : (A B C : Iface) (g : Proc B C) (f : Proc A B)
           → 𝒫._∘_ {A} {B} {C} g f
           ≡ traceᴹ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B)
                    (W.α {Neg A} {Pos B} {Neg B} {Pos C}
                       ∘ᴹ ((g ⊗ᵉ f) ∘ᴹ W.γ {Pos A} {Pos B} {Neg B} {Neg C}))
∘-computed A B C g f = refl
