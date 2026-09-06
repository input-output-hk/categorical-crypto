{-# OPTIONS --safe --without-K --guardedness #-}

-- The closed G-composite `strategyEnv B d ∘ u` as one machine with a readable
-- step.
--
-- `Adequacy` runs an induction on a `Strat` tree against the composite, so it
-- has to read the composite's step off.  `Machines.Collapse` does that for any
-- `𝒢ₚ`-composite; `kᵂ` is its `kᴳ` at this closed shape, where the two maps out
-- of `Pos unitᴵ = ⊥` are written as such.  What is left to dispatch is the
-- environment's tick, the process's answer, and the environment's answer.
--
-- Measured cost: dominated by `collapseᴳ`, priced in `Machines.Collapse`.

open import Categories.Category

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Seam

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Collapse.Absorb as Abs
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Congruence as TraceCong

module CategoricalCrypto.UC.Seam.Adequacy.Wiring where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module MT = Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module TC = TraceCong (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module 𝒫  = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The collapsed step

module _ (B : Iface) where

  -- Where the environment's two possible emissions go: a query on `B` re-enters
  -- the trace's loop, the verdict leaves on the external interface.
  outE : Neg B ⊎ Bool → (⊥ ⊎ Bool) ⊎ (Neg B ⊎ Pos B)
  outE (inj₁ n) = inj₂ (inj₁ n)
  outE (inj₂ v) = inj₁ (inj₂ v)

  outU : ⊥ ⊎ Pos B → (⊥ ⊎ Bool) ⊎ (Neg B ⊎ Pos B)
  outU (inj₁ e) = ⊥-elim e
  outU (inj₂ p) = inj₂ (inj₂ p)

module _ (B : Iface) (u : Proc unitᴵ B) where

  kᵂ : (EnvSt B × MC.St u) × ((⊥ ⊎ ⊤) ⊎ (Neg B ⊎ Pos B))
     → Dₚ ((EnvSt B × MC.St u) × ((⊥ ⊎ Bool) ⊎ (Neg B ⊎ Pos B)))
  kᵂ ((se , su) , inj₁ (inj₁ e)) = ⊥-elim e
  kᵂ ((se , su) , inj₁ (inj₂ _)) = stepˢ B (se , inj₂ tt) >>=ₚ λ q → returnₚ ((proj₁ q , su) , outE B (proj₂ q))
  kᵂ ((se , su) , inj₂ (inj₁ n)) = MC.step u (su , inj₂ n) >>=ₚ λ q → returnₚ ((se , proj₁ q) , outU B (proj₂ q))
  kᵂ ((se , su) , inj₂ (inj₂ p)) = stepˢ B (se , inj₁ p) >>=ₚ λ q → returnₚ ((proj₁ q , su) , outE B (proj₂ q))

pairedᴹ : (B : Iface) (d : Strat (Neg B) (Pos B)) (u : Proc unitᴵ B) → Proc unitᴵ Ωᴵ
pairedᴹ B d u = MT.traceᴹ (⊥ ⊎ ⊤) (⊥ ⊎ Bool) (Neg B ⊎ Pos B)
                          (MC.mk (stateˢ B d MC.⊛ MC.state u) (kᵂ B u))

------------------------------------------------------------------------
-- The composite, absorbed

private
  -- `kᴳ` and `kᵂ` differ only where `outU` reads the empty summand.
  kᴳ-kᵂ : (B : Iface) (d : Strat (Neg B) (Pos B)) (u : Proc unitᴵ B)
          (z : (EnvSt B × MC.St u) × ((⊥ ⊎ ⊤) ⊎ (Neg B ⊎ Pos B)))
        → Col.kᴳ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} (strategyEnv B d) u z ≈ₚ kᵂ B u z
  kᴳ-kᵂ B d u ((se , su) , inj₁ (inj₁ e)) = ⊥-elim e
  kᴳ-kᵂ B d u ((se , su) , inj₁ (inj₂ _)) =
    bindᶠ (λ where (_ , inj₁ _) → ≈refl
                   (_ , inj₂ _) → ≈refl)
  kᴳ-kᵂ B d u ((se , su) , inj₂ (inj₁ n)) =
    bindᶠ (λ where (_ , inj₁ e) → ⊥-elim e
                   (_ , inj₂ _) → ≈refl)
  kᴳ-kᵂ B d u ((se , su) , inj₂ (inj₂ p)) =
    bindᶠ (λ where (_ , inj₁ _) → ≈refl
                   (_ , inj₂ _) → ≈refl)

compose-≈ᴹ : (B : Iface) (d : Strat (Neg B) (Pos B)) (u : Proc unitᴵ B)
           → (strategyEnv B d 𝒫.∘ u) S.≈ᴹ pairedᴹ B d u
compose-≈ᴹ B d u =
       Abs.collapseᴳ {⊥} {⊥} {Pos B} {Neg B} {Bool} {⊤} (strategyEnv B d) u
  S.○ᴹ S.≲⇒≈ᴹ (TC.trace-resp-≲ (S.mk-cong (kᴳ-kᵂ B d u)))
