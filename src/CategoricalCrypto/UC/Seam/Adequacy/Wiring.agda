{-# OPTIONS --safe --without-K --guardedness #-}

-- The closed G-composite `strategyEnv B d ∘ u` as one machine with a readable
-- step.
--
-- `kᵂ` is `Machines.Collapse`'s `kᴳ` at this closed shape, with the two maps
-- out of `Pos unitᴵ = ⊥` written as such.
--
-- `compose-≈ᴹ` is stated at the composite's canonical collapsed representative
-- (`UC.Seam.Plug.Plugged.tracedᴹ`), avoiding the otherwise dominant conversion
-- back from the G-category's `_∘_` projection.
-- Measured warm cost: 9.9 s, down from 87 s for the named raw composite and
-- 282 s for the projected category composite.

open import Categories.Category

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Seam
open import CategoricalCrypto.UC.Seam.Plug

import CategoricalCrypto.Machines.Collapse as Col
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

------------------------------------------------------------------------
-- The collapsed step

module _ (B : Iface) where

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
           → Plugged.tracedᴹ B (strategyEnv B d) u S.≈ᴹ pairedᴹ B d u
compose-≈ᴹ B d u =
  S.≲⇒≈ᴹ (TC.trace-resp-≲ (S.mk-cong (kᴳ-kᵂ B d u)))
