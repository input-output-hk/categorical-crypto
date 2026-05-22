{-# OPTIONS --safe #-}

module CategoricalCrypto.Examples.RandomOracle where

open import categorical-crypto.Prelude hiding (_/_; _>>=_)

open import Data.Fin using (Fin)
open import Data.Vec
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_)
open import Data.Integer using (+_)
import Data.List.NonEmpty as NE

open import ProbabilisticLogic.Distribution.RationalDist renaming (_>>=ᴹ_ to _>>=_)
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import CategoricalCrypto.SFunM

------------------------------------------------------------------------
-- Uniform Dist sampling on bit-strings.

uniform-Bool : Dist-ℚ Bool
uniform-Bool = mk-Dist (((+ 1 / 2) , false) NE.∷ ((+ 1 / 2) , true) ∷ []) refl

uniform-Vec : (k : ℕ) → Dist-ℚ (Vec Bool k)
uniform-Vec zero    = return-ℚ []
uniform-Vec (suc k) = uniform-Bool >>= λ b → Dmap (b ∷_) (uniform-Vec k)

------------------------------------------------------------------------
  -- Random oracle functionality for `p` parties hashing fixed-length
-- bytestrings of length `n`.

module RandomOracle (p n : ℕ) where

  BS : Type
  BS = Vec Bool n

  uniform-BS : Dist-ℚ BS
  uniform-BS = uniform-Vec n

  Input  = Fin p × BS
  Output = Fin p × BS
  Table  = List (BS × BS)

  lookup-bs : Table → BS → Maybe BS
  lookup-bs []             _ = nothing
  lookup-bs ((k , v) ∷ xs) q with q ≟ k
  ... | yes _ = just v
  ... | no  _ = lookup-bs xs q

  step : SFunType Input Output Table
  step (s , i , q) = case lookup-bs s q of λ where
    (just h)  → return-ℚ (s , i , h)
    (nothing) → do h ← uniform-BS; return-ℚ ((q , h) ∷ s , i , h)

  Functionality : SFunᵉ {M = Dist-ℚ} Input Output
  Functionality = record
    { State = Table
    ; init  = []
    ; fun   = step
    }
