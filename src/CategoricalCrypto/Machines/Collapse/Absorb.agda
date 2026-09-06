{-# OPTIONS --safe --without-K --guardedness #-}

-- `Machines.Collapse`'s `outer`, read as a statement about `𝒢ₚ`'s own `_∘_`.
--
-- One definition, in its own module because of what it costs: projecting `_∘_`
-- out of `𝒢ₚ`'s G-construction record, which any consumer of it pays once
-- (`Machines.Base`'s header prices the same record).  Measured at 214 s warm
-- and 8 GiB — a `-M4G` cap is not enough.  Everything `Collapse` itself proves
-- stays inside `ℳₚ` and measures 13 s.

open import Categories.Category

open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_)
open import Level using (0ℓ)

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Collapse

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Congruence as TraceCong

module CategoricalCrypto.Machines.Collapse.Absorb where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module MT = Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module TC = TraceCong (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module 𝒢  = Category (𝒢ₚ 0ℓ)

-- Every object implicit is passed explicitly: left to inference, `_∘_` asks
-- Agda to invert `Machine (B⁺ + C⁻) (B⁻ + C⁺)` for the pair `(B⁺ , B⁻)`, and
-- `_+_` is not a constructor (`UC.Machine`'s `𝒫ᴵ` prices the same inversion).
collapseᴳ : {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Set}
            (g : MC.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)) (f : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
          → 𝒢._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} g f
            S.≈ᴹ MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺) (MC.mk (Sᴳ g f) (kᴳ g f))
collapseᴳ {A⁺} {A⁻} {B⁺} {B⁻} {C⁺} {C⁻} g f =
  TC.trace-resp-≈ᴹ {A⁺ ⊎ C⁻} {A⁻ ⊎ C⁺} {B⁻ ⊎ B⁺} (outer g f)
