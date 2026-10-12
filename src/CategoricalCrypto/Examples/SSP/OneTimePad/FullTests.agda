{-# OPTIONS --safe --without-K --guardedness #-}

-- OTP inlining preserves the compiled machine's equality, hence security
-- under every PM test and closure.  This does not transport `otp≤idealᵂ`
-- backwards from PM[wb]; see `docs/examples-ssp-otp.md` §4.

module CategoricalCrypto.Examples.SSP.OneTimePad.FullTests where

open import Data.Bool.Base
open import Data.Product.Base

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Examples.SSP.OneTimePad
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Semantics
open import CategoricalCrypto.UC.Bracket.InclusionTransfer
open import CategoricalCrypto.UC.Bracket.Monoidal

import CategoricalCrypto.Standard2 as Std2
import CategoricalCrypto.UC.Model.Setup as PM

private module Full = Std2.StdUC 𝒲ᴹ ι*ℰᵒ

compiled-otp compiled-real : unitᴵ Full.⇒ Full.T₀ Eveᴵ Honᴵ
compiled-otp = ⟦ otp ⟧ᵂ
compiled-real = ⟦ real ⟧ᵂ

otp≈real-full : compiled-otp Full.≈ᵁ compiled-real
otp≈real-full = Full.≈C⇒≈ᵁ (⟦⟧ᵂ-resp (≲⇒≈ᵖ otp≲real))

otp≤real-full : compiled-otp Full.≤UC compiled-real
otp≤real-full = Full.≈ᵁ⇒≤UC otp≈real-full

otp≤real-PM : Transfer.G ι⇒prot compiled-otp PM.≤UC Transfer.G ι⇒prot compiled-real
otp≤real-PM = ι-preserves-≤UC otp≤real-full

compiled-ideal : unitᴵ Full.⇒ Full.T₀ (Pollᴵ Bool) Honᴵ
compiled-ideal = ⟦ ideal ⟧ᵂ

compiled-sim : Pollᴵ Bool Full.⇒ Eveᴵ
compiled-sim = ⟦ sim ⟧ᵂ

-- The tensor here is 𝒲ᴹ's, not an asserted full-test compilation law.
ideal-with-sim : unitᴵ Full.⇒ Full.T₀ Eveᴵ Honᴵ
ideal-with-sim = Full.sub compiled-sim Full.∘ compiled-ideal

ideal-with-sim≤ideal-full : ideal-with-sim Full.≤UC compiled-ideal
ideal-with-sim≤ideal-full = Full.dummy-complete (compiled-sim , Full.≈ᵁ-refl)

ideal-with-sim≤ideal-PM : Transfer.G ι⇒prot ideal-with-sim PM.≤UC Transfer.G ι⇒prot compiled-ideal
ideal-with-sim≤ideal-PM = ι-preserves-≤UC ideal-with-sim≤ideal-full
