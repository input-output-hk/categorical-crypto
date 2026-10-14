{-# OPTIONS --safe --without-K --guardedness #-}

-- `Examples.SSP.OneTimePad`'s `otp ≤UC ideal` in PM[wb]: against
-- well-bracketed environments the compiled pad emulates the compiled secure
-- channel (`docs/examples-ssp-otp.md` §4).

module CategoricalCrypto.Examples.SSP.OneTimePad.WB where

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Examples.SSP.OneTimePad
open import CategoricalCrypto.SSP.Dense
open import CategoricalCrypto.SSP.Semantics
open import CategoricalCrypto.UC.Bracket.Setup

import CategoricalCrypto.Examples.SSP.OneTimePad.Dist as Dist
import CategoricalCrypto.SSP.Dist.Compile as Compile
import CategoricalCrypto.SSP.Setup as SSP

lazy≈realᵂ : ⟦ Dist.lazy ⟧ᵂ ≈ ⟦ real ⟧ᵂ
lazy≈realᵂ = Compile.⟦⟧ᵂ-resp-≈ᵈ Dist.lazy≈real

otp≈idealᵂ : ⟦ otp ⟧ᵂ ≈ ⟦ SSP.sub sim SSP.∘ ideal ⟧ᵂ
otp≈idealᵂ = Compile.⟦⟧ᵂ-resp-≈ᵈ Dist.otp≈idealᵈ

otp≤ideal-distᵂ : Transfer.G Compile.dist⇒PM[wb] otp ≤UC Transfer.G Compile.dist⇒PM[wb] ideal
otp≤ideal-distᵂ = Compile.preserves-≤UC Dist.otp≤ideal-dist

otp≤idealᵂ : Transfer.G SSP→PM[wb] otp ≤UC Transfer.G SSP→PM[wb] ideal
otp≤idealᵂ = otp≤ideal-distᵂ
