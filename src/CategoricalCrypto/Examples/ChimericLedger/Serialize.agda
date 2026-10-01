{-# OPTIONS --safe --without-K --guardedness #-}

-- One concrete serializer, so that `SerInj` is a theorem rather than a
-- hypothesis.  It is literal: reordering a transaction's inputs changes its
-- encoding, as it must, since `SerInj` is about `_≡_` on `Tx`.

open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Vec.Base
open import Relation.Binary.PropositionalEquality

open import Data.Bits.Codec

open import CategoricalCrypto.Examples.ChimericLedger

import CategoricalCrypto.Examples.ChimericLedger.Property as Property

module CategoricalCrypto.Examples.ChimericLedger.Serialize where

txCodec : (n : ℕ) → Codec (Ledger.Tx n)
txCodec n = ×-codec (list-codec (×-codec (vec-codec bool-codec n) ℕ-codec))
              (×-codec (list-codec ℕ²-codec) (list-codec ℕ²-codec))
  where
  ℕ²-codec : Codec (ℕ × ℕ)
  ℕ²-codec = ×-codec ℕ-codec ℕ-codec

ser : (n : ℕ) → Ledger.Tx n → List Bool
ser n = Codec.encode (txCodec n)

open Property ser

serInj : SerInj
serInj n = Codec.encode-injective (txCodec n)

ideal-preserves-valueˢ : (a V : ℕ) → PreservesValue (genesisTotal V) (Ideal a V)
ideal-preserves-valueˢ a V = ideal-preserves-value a V serInj

------------------------------------------------------------------------
-- Boundary cases
------------------------------------------------------------------------

-- An empty transaction is three empty lists, each a unary length `0`.
ser-empty : ser 1 ([] , [] , []) ≡ false ∷ false ∷ false ∷ []
ser-empty = refl

-- A zero-valued output in the third component versus the same pair as a
-- withdrawal in the second: what raw concatenation would confuse.
outs-not-wdrls : ser 1 ([] , [] , (0 , 0) ∷ []) ≢ ser 1 ([] , (0 , 0) ∷ [] , [])
outs-not-wdrls ()

-- Zero-valued fields do not shift the boundary between a pair's components.
addr-not-value : ser 1 ([] , [] , (0 , 1) ∷ []) ≢ ser 1 ([] , [] , (1 , 0) ∷ [])
addr-not-value ()

-- One output versus two whose encodings concatenate to the same bits.
one-out-not-two : ser 1 ([] , [] , (1 , 0) ∷ []) ≢ ser 1 ([] , [] , (0 , 0) ∷ (0 , 0) ∷ [])
one-out-not-two ()

-- A hash is spent at its fixed width, with the index reading on from there.
txᵗ : Ledger.Tx 1
txᵗ = ((true ∷ [] , 2) ∷ []) , ((3 , 1) ∷ []) , ((4 , 1) ∷ [])

round-trip : Codec.decode (txCodec 1) (ser 1 txᵗ) ≡ just (txᵗ , [])
round-trip = refl

