{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Machines.Positive.Wires.Gamma where

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
  repack-γ : repack (PW.γ {A} {B} {C} {D}) QS.≈ᴹ QW.γ {A} {B} {C} {D}
  repack-γ {A} {B} {C} {D} =
    mapped-compose {g = a₆} {f = a₅ P.∘ᴹ a₄ P.∘ᴹ a₃ P.∘ᴹ a₂ P.∘ᴹ a₁ P.∘ᴹ a₀}
      {g′ = repack a₆} {f′ = repack a₅ Q.∘ᴹ repack a₄ Q.∘ᴹ repack a₃ Q.∘ᴹ repack a₂ Q.∘ᴹ repack a₁ Q.∘ᴹ repack a₀} QS.reflᴹ
      (mapped-compose {g = a₅} {f = a₄ P.∘ᴹ a₃ P.∘ᴹ a₂ P.∘ᴹ a₁ P.∘ᴹ a₀}
        {g′ = repack a₅} {f′ = repack a₄ Q.∘ᴹ repack a₃ Q.∘ᴹ repack a₂ Q.∘ᴹ repack a₁ Q.∘ᴹ repack a₀} QS.reflᴹ
        (mapped-compose {g = a₄} {f = a₃ P.∘ᴹ a₂ P.∘ᴹ a₁ P.∘ᴹ a₀}
          {g′ = repack a₄} {f′ = repack a₃ Q.∘ᴹ repack a₂ Q.∘ᴹ repack a₁ Q.∘ᴹ repack a₀} QS.reflᴹ
          (mapped-compose {g = a₃} {f = a₂ P.∘ᴹ a₁ P.∘ᴹ a₀}
            {g′ = repack a₃} {f′ = repack a₂ Q.∘ᴹ repack a₁ Q.∘ᴹ repack a₀} QS.reflᴹ
            (mapped-compose {g = a₂} {f = a₁ P.∘ᴹ a₀}
              {g′ = repack a₂} {f′ = repack a₁ Q.∘ᴹ repack a₀} QS.reflᴹ
              (mapped-compose {g = a₁} {f = a₀} {g′ = repack a₁} {f′ = repack a₀} QS.reflᴹ QS.reflᴹ)))))
    where
    a₀ : P.Machine ((A ⊎ D) ⊎ (C ⊎ B)) ((A ⊎ D) ⊎ (B ⊎ C))
    a₀ = PMM.id PT.⊗ᵉ PB.σ⇒
    a₁ : P.Machine ((A ⊎ D) ⊎ (B ⊎ C)) (A ⊎ (D ⊎ (B ⊎ C)))
    a₁ = PWires.α⇒
    a₂ : P.Machine (A ⊎ (D ⊎ (B ⊎ C))) (A ⊎ ((D ⊎ B) ⊎ C))
    a₂ = PMM.id PT.⊗ᵉ PWires.α⇐
    a₃ : P.Machine (A ⊎ ((D ⊎ B) ⊎ C)) (A ⊎ ((B ⊎ D) ⊎ C))
    a₃ = PMM.id PT.⊗ᵉ (PB.σ⇒ PT.⊗ᵉ PMM.id)
    a₄ : P.Machine (A ⊎ ((B ⊎ D) ⊎ C)) ((A ⊎ (B ⊎ D)) ⊎ C)
    a₄ = PWires.α⇐
    a₅ : P.Machine ((A ⊎ (B ⊎ D)) ⊎ C) (((B ⊎ D) ⊎ A) ⊎ C)
    a₅ = PB.σ⇒ PT.⊗ᵉ PMM.id
    a₆ : P.Machine (((B ⊎ D) ⊎ A) ⊎ C) ((B ⊎ D) ⊎ (A ⊎ C))
    a₆ = PWires.α⇒
