{-# OPTIONS --safe --without-K --guardedness #-}

-- The UC setup at the machine model, as closed terms: the eight grading laws
-- are now theorems (four in `UC.Machine.Dictionary`, four in
-- `UC.Machine.Laws.*`), so `UC.Machine.Grading.Gradingᴹ` and
-- `UC.Machine.UCBaseᴹ` apply, and `𝒫ᴵ` is a `UCBase` with nothing owed.
--
-- Measured warm: 2881 s, and the reason is the one
-- `UC.Machine.Cast.Tensor` records once more.  `GradingLawsᴹ`'s field types are
-- written with `UC.Machine.Grading`'s own `private module 𝒫` and the law
-- modules' with theirs, so for the four trace-touching fields the two spellings
-- differ by exactly that alias over a `𝒫ᴵ`-COMPOSITE — four conversions, one
-- per field.  Sharing a single `𝒫` alias across `…Grading` and `…Laws.*` would
-- make all four syntactic; that cut is named in `docs/protocol-rewrite.md` and
-- not taken here, because it re-prices eight green modules.

open import Level using (0ℓ; suc)

open import CategoricalCrypto.UC.Core using (Grading; UCBase)
open import CategoricalCrypto.UC.Machine using (𝒫ᴵ; UCBaseᴹ)
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Grading
open import CategoricalCrypto.UC.Machine.Laws.Assoc
open import CategoricalCrypto.UC.Machine.Laws.Nat
open import CategoricalCrypto.UC.Machine.Laws.Relay
open import CategoricalCrypto.UC.Machine.Laws.Simulator

module CategoricalCrypto.UC.Machine.Setup where

gradingLawsᴹ : GradingLawsᴹ
gradingLawsᴹ = record
  { T₁-resp-≈  = T₁-resp-≈ᴹ
  ; T₁-id      = T₁-idᴹ
  ; T₁-∘       = T₁-∘ᴹ
  ; sub-resp-≈ = sub-resp-≈ᴹ
  ; sub-id     = sub-idᴹ
  ; sub-∘      = sub-∘ᴹ
  ; a-isoˡ     = a-isoˡᴹ
  ; a-nat      = a-natᴹ
  }

gradingᴹ : Grading 𝒫ᴵ
gradingᴹ = Gradingᴹ gradingLawsᴹ

ucBaseᴹ : UCBase (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) 0ℓ 0ℓ
ucBaseᴹ = UCBaseᴹ gradingᴹ
