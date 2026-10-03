{-# OPTIONS --safe --without-K #-}

-- Existential collapse at a class of small errors.
--
-- A class containing zero and closed under addition is all `∼Small` needs:
-- those two are exactly its reflexivity and its transitivity, so nothing about
-- approaching zero is assumed and no halving is spent.
--
-- `UC.Approximate.Local._∼ᴺ_` IS this relation at the negligible class over
-- rational sequences, and takes its equivalence from here.

open import Data.Product.Base
open import Level
open import Relation.Binary.Structures

open import CategoricalCrypto.Approx.Error

module CategoricalCrypto.Approx.Small
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E
open import CategoricalCrypto.Approx.Space E

record SmallClass (ℓs : Level) : Set (es ⊔ suc ℓs) where
  field
    Small    : Error → Set ℓs
    small-ε₀ : Small ε₀
    small-⊕  : {ε δ : Error} → Small ε → Small δ → Small (ε ⊕ δ)

module Collapse {ℓs : Level} (S : SmallClass ℓs) (c ℓa : Level) where

  open SmallClass S

  module _ (X : ApproxSpace c ℓa) where
    open ApproxSpace X

    infix 4 _∼Small_

    _∼Small_ : Carrier → Carrier → Set (es ⊔ ℓs ⊔ ℓa)
    x ∼Small y = Σ[ ε ∈ Error ] (Small ε × x ≈[ ε ] y)

    ∼Small-isEquivalence : IsEquivalence _∼Small_
    ∼Small-isEquivalence = record
      { refl  = ε₀ , small-ε₀ , ≈[]-refl
      ; sym   = λ (ε , sε , h) → ε , sε , ≈[]-sym h
      ; trans = λ (ε , sε , h) (δ , sδ , k) → ε ⊕ δ , small-⊕ sε sδ , ≈[]-trans h k
      }
