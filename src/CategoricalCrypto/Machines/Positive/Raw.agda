{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Machines.Positive.Raw where

open import Categories.Category.Monoidal.Bundle
import Categories.GConstruction as GC
import Categories.GConstructionMonoidal as GM
import Categories.GConstructionTrace as GT
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_)
open import Level
import CategoricalCrypto.Machines.Base as PM
import CategoricalCrypto.Machines.Positive.Base as Positive
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Bundle as Bundle
import CategoricalCrypto.Machines.G as GImpl

module At (ℓ : Level) where
  open Re.At ℓ
  module PG = MonoidalCategory (PM.𝒢ₚᴹ ℓ)
  module QG = MonoidalCategory (Positive.𝒢₊ᴹ ℓ)
  module PC = MCat (PM.𝒱ₚ ℓ) (PM.𝒫ₚ ℓ)
  module QC = MCat (Positive.𝒱₊ ℓ) (Positive.𝒫₊ ℓ)
  module PB = Bundle (PM.𝒱ₚ ℓ) (PM.distₚ ℓ) (PM.𝒫ₚ ℓ)
  module QB = Bundle (Positive.𝒱₊ ℓ) (Positive.dist₊ ℓ) (Positive.𝒫₊ ℓ)
  module PI = GImpl (PM.𝒱ₚ ℓ) (PM.distₚ ℓ) (PM.𝒫ₚ ℓ) (PM.Elgotₚ ℓ)
  module QI = GImpl (Positive.𝒱₊ ℓ) (Positive.dist₊ ℓ) (Positive.𝒫₊ ℓ) (Positive.Elgot₊ ℓ)
  module PW = GT PC.Mealy-Category PB.Mealy-Monoidal PI.Mealy-Traced
  module QW = GT QC.Mealy-Category QB.Mealy-Monoidal QI.Mealy-Traced
  private variable A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ D⁺ D⁻ : Set ℓ

  opaque
    composeₚ : P.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺) → P.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)
             → P.Machine (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺)
    composeₚ {B⁺} {C⁻} {B⁻} {C⁺} {A⁺} {A⁻} g f =
      GC.composeᴳ PC.Mealy-Category PB.Mealy-Monoidal PI.Mealy-Traced {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} g f

    compose₊ : Q.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺) → Q.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)
             → Q.Machine (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺)
    compose₊ {B⁺} {C⁻} {B⁻} {C⁺} {A⁺} {A⁻} g f =
      GC.composeᴳ QC.Mealy-Category QB.Mealy-Monoidal QI.Mealy-Traced {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} g f

    tensorₚ : P.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺) → P.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺)
            → P.Machine ((A⁺ ⊎ C⁺) ⊎ (B⁻ ⊎ D⁻)) ((A⁻ ⊎ C⁻) ⊎ (B⁺ ⊎ D⁺))
    tensorₚ {A⁺} {B⁻} {A⁻} {B⁺} {C⁺} {D⁻} {C⁻} {D⁺} f g =
      GM._⊗₁ᴳ_ PC.Mealy-Category PB.Mealy-Monoidal PI.Mealy-Traced {A⁺} {A⁻} {B⁺} {B⁻} {C⁺} {C⁻} {D⁺} {D⁻} f g

    tensor₊ : Q.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺) → Q.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺)
            → Q.Machine ((A⁺ ⊎ C⁺) ⊎ (B⁻ ⊎ D⁻)) ((A⁻ ⊎ C⁻) ⊎ (B⁺ ⊎ D⁺))
    tensor₊ {A⁺} {B⁻} {A⁻} {B⁺} {C⁺} {D⁻} {C⁻} {D⁺} f g =
      GM._⊗₁ᴳ_ QC.Mealy-Category QB.Mealy-Monoidal QI.Mealy-Traced {A⁺} {A⁻} {B⁺} {B⁻} {C⁺} {C⁻} {D⁺} {D⁻} f g

  opaque
    unfolding composeₚ compose₊ GC.composeᴳ

    composeₚ-raw : (g : P.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)) (f : P.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
      → composeₚ g f PS.≈ᴹ PTr.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺)
          (PW.α P.∘ᴹ ((g PT.⊗ᵉ f) P.∘ᴹ PW.γ))
    composeₚ-raw g f = PS.reflᴹ

    compose₊-raw : (g : Q.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)) (f : Q.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
      → compose₊ g f QS.≈ᴹ QTr.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺)
          (QW.α Q.∘ᴹ ((g QT.⊗ᵉ f) Q.∘ᴹ QW.γ))
    compose₊-raw g f = QS.reflᴹ

  opaque
    unfolding tensorₚ tensor₊ GM._⊗₁ᴳ_

    tensorₚ-raw : (f : P.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) (g : P.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺))
      → tensorₚ f g PS.≈ᴹ (PW.mid P.∘ᴹ ((f PT.⊗ᵉ g) P.∘ᴹ PW.mid))
    tensorₚ-raw f g = PS.reflᴹ

    tensor₊-raw : (f : Q.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) (g : Q.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺))
      → tensor₊ f g QS.≈ᴹ (QW.mid Q.∘ᴹ ((f QT.⊗ᵉ g) Q.∘ᴹ QW.mid))
    tensor₊-raw f g = QS.reflᴹ

  opaque
    unfolding composeₚ compose₊ tensorₚ tensor₊

    composeₚ-project : (g : P.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)) (f : P.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
      → composeₚ g f PS.≈ᴹ PG._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} g f
    composeₚ-project g f = PS.reflᴹ

    compose₊-project : (g : Q.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)) (f : Q.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
      → compose₊ g f QS.≈ᴹ QG._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} g f
    compose₊-project g f = QS.reflᴹ

    tensorₚ-project : (f : P.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) (g : P.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺))
      → tensorₚ f g PS.≈ᴹ PG._⊗₁_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} {D⁺ , D⁻} f g
    tensorₚ-project f g = PS.reflᴹ

    tensor₊-project : (f : Q.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) (g : Q.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺))
      → tensor₊ f g QS.≈ᴹ QG._⊗₁_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} {D⁺ , D⁻} f g
    tensor₊-project f g = QS.reflᴹ

  compose₊-cong : {g h : Q.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)} {f i : Q.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)}
    → g QS.≈ᴹ h → f QS.≈ᴹ i → compose₊ g f QS.≈ᴹ compose₊ h i
  compose₊-cong {B⁺} {C⁻} {B⁻} {C⁺} {A⁺} {A⁻} {g} {h} {f} {i} p q =
    QS._○ᴹ_ (compose₊-project g f)
      (QS._○ᴹ_ (QG.∘-resp-≈ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} p q)
        (QS.⟺ᴹ (compose₊-project h i)))

  tensor₊-cong : {f h : Q.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)} {g i : Q.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺)}
    → f QS.≈ᴹ h → g QS.≈ᴹ i → tensor₊ f g QS.≈ᴹ tensor₊ h i
  tensor₊-cong {A⁺} {B⁻} {A⁻} {B⁺} {C⁺} {D⁻} {C⁻} {D⁺} {f} {h} {g} {i} p q =
    QS._○ᴹ_ (tensor₊-project f g)
      (QS._○ᴹ_ (QG.⊗.F-resp-≈ {A = (A⁺ , A⁻) , (C⁺ , C⁻)} {B = (B⁺ , B⁻) , (D⁺ , D⁻)} (p , q))
        (QS.⟺ᴹ (tensor₊-project h i)))
