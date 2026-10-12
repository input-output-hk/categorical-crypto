{-# OPTIONS --safe --without-K --guardedness #-}

-- Full-context OTP inlining and the compiled simulator construction cross
-- the observation restriction and its composite with `q`. These premises
-- come from `FullTests`, not from PM[wb]'s confidentiality theorem.

module CategoricalCrypto.Examples.SSP.OneTimePad.ObservationRestriction where

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Examples.SSP.OneTimePad.FullTests
open import CategoricalCrypto.UC.Bracket.ObservationRestriction

import CategoricalCrypto.UC.Bracket.Setup as WB

otp≤real-restricted : compiled-otp WB.𝒲ᵂ.≤UC compiled-real
otp≤real-restricted = full-≤UC⇒wb-≤UC otp≤real-full

otp≤real-coarsened : Transfer.G full⇒PM[wb] compiled-otp WB.≤UC Transfer.G full⇒PM[wb] compiled-real
otp≤real-coarsened = full-preserves-≤UC otp≤real-full

ideal-with-sim≤ideal-coarsened : Transfer.G full⇒PM[wb] ideal-with-sim WB.≤UC Transfer.G full⇒PM[wb] compiled-ideal
ideal-with-sim≤ideal-coarsened = full-preserves-≤UC ideal-with-sim≤ideal-full
