{-# OPTIONS --safe --without-K #-}

-- Approximate spaces: a carrier with closeness at an error.  `resp₀` says a
-- fixed bound survives a zero-error change of either endpoint, so zero error
-- (`zeroSetoid`) is the one fine equality a space carries.

open import Level
open import Relation.Binary.Bundles

open import CategoricalCrypto.Approx.Error

module CategoricalCrypto.Approx.Space {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E

private variable c ℓa : Level

record ApproxSpace (c ℓa : Level) : Set (suc (c ⊔ ℓa) ⊔ es ⊔ ℓe) where
  field
    Carrier : Set c
    approx  : Approximation Carrier E ℓa

  -- `Approximation` re-exports its error algebra, which the module parameter
  -- already fixes; taking only the relation keeps the two spellings apart.
  open Approximation approx public using (_≈[_]_; ≈[]-refl; ≈[]-sym; ≈[]-trans; ≈[]-mono)

  ≈[]-trans₀ : {x y z : Carrier} → x ≈[ ε₀ ] y → y ≈[ ε₀ ] z → x ≈[ ε₀ ] z
  ≈[]-trans₀ h k = ≈[]-mono ⊕-identityˡ (≈[]-trans h k)

module _ (X : ApproxSpace c ℓa) where
  open ApproxSpace X

  resp₀ : {x x′ y y′ : Carrier} {ε : Error}
        → x′ ≈[ ε₀ ] x → y ≈[ ε₀ ] y′ → x ≈[ ε ] y → x′ ≈[ ε ] y′
  resp₀ = ≈[]-resp₀ E approx

  zeroSetoid : Setoid c ℓa
  zeroSetoid = record
    { Carrier = Carrier
    ; _≈_ = λ x y → x ≈[ ε₀ ] y
    ; isEquivalence = record { refl = ≈[]-refl ; sym = ≈[]-sym ; trans = ≈[]-trans₀ }
    }
