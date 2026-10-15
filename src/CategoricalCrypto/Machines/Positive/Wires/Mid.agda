{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Machines.Positive.Wires.Mid where

import Categories.GConstructionTrace as GT
import Categories.Category.Monoidal.Utilities as MU
import Categories.Category.Monoidal.Braided.Properties as BP
open import Data.Sum.Base using (_⊎_)
open import Level
import CategoricalCrypto.Machines.Base as PM
import CategoricalCrypto.Machines.Positive.Base as Positive
import CategoricalCrypto.Machines.Positive.Repack as Re

module _ (ℓ : Level) where
  open Re.At ℓ
  module PW = GT PMM.U PMM.monoidal (PM.Tracedₚ ℓ)
  module QW = GT QMM.U QMM.monoidal (Positive.Traced₊ ℓ)
  module PWires = MU.Shorthands PMM.monoidal
  module PB = BP.Shorthands PMM.braided
  private variable A B C D : Set ℓ
  repack-mid : repack (PW.mid {A} {B} {C} {D}) QS.≈ᴹ QW.mid {A} {B} {C} {D}
  repack-mid {A} {B} {C} {D} =
    mapped-compose {g = PWires.α⇐} {f = (PMM.id PT.⊗ᵉ inner) P.∘ᴹ PWires.α⇒} QS.reflᴹ
      (mapped-compose {g = PMM.id PT.⊗ᵉ inner} {f = PWires.α⇒}
        (mapped-tensor {f = PMM.id} {g = inner} QS.reflᴹ
          (mapped-compose {g = PWires.α⇒} {f = (PB.σ⇒ PT.⊗ᵉ PMM.id) P.∘ᴹ PWires.α⇐} QS.reflᴹ
            (mapped-compose {g = PB.σ⇒ PT.⊗ᵉ PMM.id} {f = PWires.α⇐} QS.reflᴹ QS.reflᴹ))) QS.reflᴹ)
    where
    inner : P.Machine (B ⊎ (C ⊎ D)) (C ⊎ (B ⊎ D))
    inner = PWires.α⇒ P.∘ᴹ (PB.σ⇒ PT.⊗ᵉ PMM.id) P.∘ᴹ PWires.α⇐
