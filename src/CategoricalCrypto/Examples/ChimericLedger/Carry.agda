{-# OPTIONS --safe --without-K --guardedness #-}

-- `pov-transfer`'s premise, supplied by the seam: `UC.Seam.Carry.agreeToAdv`
-- turns an environment agreement between the two variants' machine images into
-- the `_≈adv[_]_` the example's transfer lemma consumes.  Additions only — the
-- example is untouched, and this is the whole of what the machine layer buys
-- it.
--
-- `advᴸ` names that advantage once rather than inlining it, and that is not
-- taste: the two systems are concrete here, and the seam left as a SUBTERM of
-- `pov-transfer`'s argument does not finish in 1750 s, where naming it makes the
-- whole module a 16 s warm check.  Same lever as `UC.Seam`'s header records for
-- the observations.

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.UC.Seam
open import CategoricalCrypto.UC.Seam.Carry

import CategoricalCrypto.Examples.ChimericLedger.POV as POV

module CategoricalCrypto.Examples.ChimericLedger.Carry
  (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) where

open Ledger ℓ
open POV ℓ ser

-- What an emulation of one variant by the other has to show at the machine
-- layer: the embedded strategies cannot separate the two images.
Emulᴸ : Variant → Variant → LState → Set
Emulᴸ v₁ v₂ s₀ = Agreeˢ LedgerIf (morphism (Sys v₁ s₀)) (morphism (Sys v₂ s₀))

advᴸ : (v₁ v₂ : Variant) (s₀ : LState) → Emulᴸ v₁ v₂ s₀ → (δ : ℚ) → 0ℚ ℚ.< δ
     → Sys v₁ s₀ ≈adv[ (λ _ → δ) ] Sys v₂ s₀
advᴸ v₁ v₂ s₀ = agreeToAdv (Sys v₁ s₀) (Sys v₂ s₀)

pov-carryᴸ : (v₁ v₂ : Variant) (s₀ : LState) → Emulᴸ v₁ v₂ s₀
           → {ε : ℕ → ℚ} (δ : ℚ) → 0ℚ ℚ.< δ
           → POVaudit v₁ s₀ ε → POVaudit v₂ s₀ (λ q → ε q ℚ.+ δ)
pov-carryᴸ v₁ v₂ s₀ ag δ δ>0 = pov-transfer v₁ v₂ s₀ (advᴸ v₁ v₂ s₀ ag δ δ>0)
