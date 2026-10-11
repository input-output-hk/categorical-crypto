{-# OPTIONS --safe --without-K --guardedness #-}

-- The symmetry of the sealed machine bundle `𝔾ᵒ`: the G construction's
-- braiding (`Categories.GConstructionSymmetric`) at the application `𝒢ₚᴹ` is
-- built from, sealed as `𝔾ᵒ` is (`UC.Model.Seal`'s disciplines).  The seal
-- covers the whole `Symmetric` structure and is typed against `𝔾ᵒ`'s own
-- monoidal field, so `𝔾ˢ` re-assembles nothing but opaque projections: its
-- underlying monoidal category is `𝔾ᵒ` up to record eta, and a `StdUC` built
-- from it is `UC.Model.Setup`'s.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

open import Level

import Categories.GConstructionSymmetric as GS

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.UC.Model.Seal

import CategoricalCrypto.Machines.Bundle as Bundle
import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.G as G

module CategoricalCrypto.UC.Model.Symmetric where

opaque
  unfolding 𝔾ᵒ

  -- The arguments are `Machines.G.Mealy-Gᴹ`'s, spelled as there, so that the
  -- monoidal structure this is typed against is syntactically `𝔾ᵒ`'s.
  symmetricᵒ : Symmetric (MonoidalCategory.monoidal 𝔾ᵒ)
  symmetricᵒ = GS.GConstructionSymmetric
    (MCat.Mealy-Category (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)) (Bundle.Mealy-Monoidal (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ))
    (G.Mealy-Traced (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)) (G.Mealy-TraceLaws (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ))

𝔾ˢ : SymmetricMonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
𝔾ˢ = record { U = ∣𝔾ᵒ∣ ; monoidal = MonoidalCategory.monoidal 𝔾ᵒ ; symmetric = symmetricᵒ }
