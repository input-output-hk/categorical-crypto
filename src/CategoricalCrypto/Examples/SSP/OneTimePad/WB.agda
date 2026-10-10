{-# OPTIONS --safe --without-K --guardedness #-}

-- `Examples.SSP.OneTimePad`'s `otp ≤UC ideal` in PM[wb]: against
-- well-bracketed environments the compiled pad emulates the compiled secure
-- channel (`docs/examples-ssp-otp.md` §4).

module CategoricalCrypto.Examples.SSP.OneTimePad.WB where

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Examples.SSP.OneTimePad
open import CategoricalCrypto.SSP.Dense
open import CategoricalCrypto.SSP.Dense.Tests
open import CategoricalCrypto.UC.Bracket.Setup

otp≤idealᵂ : Transfer.G SSP→PM[wb] otp ≤UC Transfer.G SSP→PM[wb] ideal
otp≤idealᵂ = preserves-≤UC otp≤ideal
