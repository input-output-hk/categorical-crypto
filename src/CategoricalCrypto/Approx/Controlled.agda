{-# OPTIONS --safe --without-K #-}

-- Controlled maps: the resource-aware morphisms of approximate spaces.
--
-- A nonexpansive map keeps its bound; a resource-sensitive pullback TRANSFORMS
-- it, and the transformation is part of the morphism rather than a side
-- condition on it.
--
-- A `Control` is a monotone map of the error preorder (stdlib's
-- `PreorderHomomorphism`) that does not raise zero and is subadditive.
--
-- Everything is stated with `⊑`, in the direction that makes a BOUND
-- admissible: the intended model's allowance substitutions are equations
-- (`Data.Nat.Positive.scale-·`, `scale-comm`), but a model whose resource
-- certificates only bound an allowance from above reads them through an
-- inequality, and demanding equations here would exclude it.

open import Level
open import Relation.Binary.Morphism.Bundles

import Relation.Binary.Morphism.Construct.Identity as Id

open import CategoricalCrypto.Approx.Error

module CategoricalCrypto.Approx.Controlled
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E
open import CategoricalCrypto.Approx.Space E

private variable c ℓa : Level

------------------------------------------------------------------------
-- The error transformations a morphism may carry

record Control : Set (es ⊔ ℓe) where
  field homomorphism : PreorderHomomorphism ⊑-preorder ⊑-preorder

  open PreorderHomomorphism homomorphism public renaming (⟦_⟧ to at)

  field
    preserves-ε₀ : at ε₀ ⊑ ε₀
    preserves-⊕  : {ε δ : Error} → at (ε ⊕ δ) ⊑ at ε ⊕ at δ

open Control

idᶜ : Control
idᶜ = record
  { homomorphism = Id.preorderHomomorphism ⊑-preorder ; preserves-ε₀ = ⊑-refl ; preserves-⊕ = ⊑-refl }

------------------------------------------------------------------------
-- …and the morphisms carrying them

record Controlled (X Y : ApproxSpace c ℓa) : Set (c ⊔ es ⊔ ℓe ⊔ ℓa) where
  private
    module X = ApproxSpace X
    module Y = ApproxSpace Y

  field
    map       : X.Carrier → Y.Carrier
    control   : Control
    preserves : {x y : X.Carrier} {ε : Error}
              → x X.≈[ ε ] y → map x Y.≈[ at control ε ] map y
