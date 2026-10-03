{-# OPTIONS --safe --without-K --guardedness #-}

-- `qb-∘` at the real `𝒫ᴵ` composite: `UC.Machine.Composite` discharges
-- `Unfolding` for it, and the walk of `UC.QueryBound.Compose` does the rest.
-- Congruence is paid by the hom-level closure in `Compose.Laws`, not by this
-- concrete step.

open import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Level

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Composite
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.QueryBound.Compose

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Pointwise as Pw

module CategoricalCrypto.UC.QueryBound.Compose.Step where

open Core (𝒱ₚ 0ℓ)

module _ (A B C : Iface) (g : Proc B C) (f : Proc A B) where

  private
    module QC = Compose {A} {B} {C} (St g) (St f) (point (state g) tt) (point (state f) tt)
                        (pointᶜ A B C g f) (step g) (step f) (stepᶜ A B C g f) (solveᶜ A B C g f)

  qbᵢ-∘ : {c c′ : ℕ} → Certified {B} {C} c g → Certified {A} {B} c′ f
        → QB {A} {C} (c ℕ.* c′)
            (Col.MT.traceᴹ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B)
              (Col.W.α MC.∘ᴹ ((g Pw.T.⊗ᵉ f) MC.∘ᴹ Col.W.γ)))
  qbᵢ-∘ qg qf = Nᶜ A B C g f , QC.qbᵢ-∘ᵍ (unfoldᶜ A B C g f) qg qf , eqᶜ A B C g f
