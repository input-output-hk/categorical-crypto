{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Machines.Positive.Bridge where

import Categories.GConstructionTrace as GT

open import Data.Sum.Base using (_⊎_)
open import Level

import CategoricalCrypto.Machines.Base as PM
import CategoricalCrypto.Machines.Positive.Base as Positive
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.Machines.Positive.Raw as Raw
import CategoricalCrypto.Machines.Positive.Wires.Alpha as WA
import CategoricalCrypto.Machines.Positive.Wires.Gamma as WG
import CategoricalCrypto.Machines.Positive.Wires.Mid as WM

module _ (ℓ : Level) where
  open Re.At ℓ
  module G = Raw.At ℓ
  module PW = G.PW
  module QW = G.QW
  private variable A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ D⁺ D⁻ : Set ℓ

  repack-compose : (g : P.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)) (f : P.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
    → repack (G.composeₚ g f) QS.≈ᴹ G.compose₊ (repack g) (repack f)
  repack-compose {B⁺} {C⁻} {B⁻} {C⁺} {A⁺} {A⁻} g f =
    let a = PW.α {A⁻} {B⁺} {B⁻} {C⁺}
        c = PW.γ {A⁺} {B⁺} {B⁻} {C⁻}
        a′ = QW.α {A⁻} {B⁺} {B⁻} {C⁺}
        c′ = QW.γ {A⁺} {B⁺} {B⁻} {C⁻}
        w = a P.∘ᴹ ((g PT.⊗ᵉ f) P.∘ᴹ c)
        w′ = a′ Q.∘ᴹ ((repack g QT.⊗ᵉ repack f) Q.∘ᴹ c′)
    in QS._○ᴹ_ (repack-resp (G.composeₚ-raw g f))
      (QS._○ᴹ_ (repack-trace {A = A⁺ ⊎ C⁻} {X = B⁻ ⊎ B⁺} {B = A⁻ ⊎ C⁺} w)
        (QS._○ᴹ_ (QTC.trace-resp-≈ᴹ {A⁺ ⊎ C⁻} {A⁻ ⊎ C⁺} {B⁻ ⊎ B⁺} {f = repack w} {g = w′}
          (mapped-compose {g = a} {f = (g PT.⊗ᵉ f) P.∘ᴹ c}
            {g′ = a′} {f′ = (repack g QT.⊗ᵉ repack f) Q.∘ᴹ c′} (WA.repack-α ℓ)
            (mapped-compose {g = g PT.⊗ᵉ f} {f = c}
              {g′ = repack g QT.⊗ᵉ repack f} {f′ = c′}
              (repack-mealy-tensor g f) (WG.repack-γ ℓ))))
          (QS.⟺ᴹ (G.compose₊-raw (repack g) (repack f)))))

  repack-tensor : (f : P.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) (g : P.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺))
    → repack (G.tensorₚ f g) QS.≈ᴹ G.tensor₊ (repack f) (repack g)
  repack-tensor {A⁺} {B⁻} {A⁻} {B⁺} {C⁺} {D⁻} {C⁻} {D⁺} f g =
    let a = PW.mid {A⁻} {B⁺} {C⁻} {D⁺}
        c = PW.mid {A⁺} {C⁺} {B⁻} {D⁻}
        a′ = QW.mid {A⁻} {B⁺} {C⁻} {D⁺}
        c′ = QW.mid {A⁺} {C⁺} {B⁻} {D⁻}
    in QS._○ᴹ_ (repack-resp (G.tensorₚ-raw f g))
      (QS._○ᴹ_ (mapped-compose {g = a} {f = (f PT.⊗ᵉ g) P.∘ᴹ c}
        {g′ = a′} {f′ = (repack f QT.⊗ᵉ repack g) Q.∘ᴹ c′} (WM.repack-mid ℓ)
        (mapped-compose {g = f PT.⊗ᵉ g} {f = c}
          {g′ = repack f QT.⊗ᵉ repack g} {f′ = c′}
          (repack-mealy-tensor f g) (WM.repack-mid ℓ)))
        (QS.⟺ᴹ (G.tensor₊-raw (repack f) (repack g))))
