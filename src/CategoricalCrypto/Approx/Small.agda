{-# OPTIONS --safe --without-K #-}

-- Existential collapse at a class of small errors
-- (`docs/quantitative-uc-setup-plan.typ` §8).
--
-- `x ∼Small y` asserts that SOME error of the class separates the two.  A class
-- containing zero and closed under addition is all this needs: those two are
-- exactly reflexivity and transitivity, so nothing about approaching zero is
-- assumed and no halving is spent.
--
-- This is NOT the all-positive collapse of `Approx.Forget`.  Taking `Small` to
-- be everything gives mere existence of a bound, which is indiscrete wherever
-- every pair admits one — as it is for a bounded observation distance — so it
-- does not generally recover the intended qualitative observation.  The two
-- collapses are kept apart deliberately.
--
-- `UC.Approximate.Local._∼ᴺ_` IS this relation at the negligible class over
-- rational sequences, and takes its equivalence from here.
--
-- The controlled half — which controls preserve the class, and the collapse on
-- the wide subcategory they cut out — is `Approx.Small.Controlled`, kept apart
-- so that a consumer of the RELATION does not pay for `SubCategory`.

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)

open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra)

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

  open SmallClass S public

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

  smallSetoid : ApproxSpace c ℓa → Setoid c (es ⊔ ℓs ⊔ ℓa)
  smallSetoid X = record
    { Carrier = ApproxSpace.Carrier X
    ; _≈_ = _∼Small_ X
    ; isEquivalence = ∼Small-isEquivalence X
    }

  -- Reflexivity with the space named: `Carrier` is a projection, so a functor
  -- law cannot recover it by unification.
  ∼Small-refl : (X : ApproxSpace c ℓa) {x : ApproxSpace.Carrier X} → _∼Small_ X x x
  ∼Small-refl X = ε₀ , small-ε₀ , ApproxSpace.≈[]-refl X

  FSmall : Functor (Approx c ℓa) (Setoids c (es ⊔ ℓs ⊔ ℓa))
  FSmall = record
    { F₀ = smallSetoid
    ; F₁ = λ f → record
        { to = Nonexpansive.map f
        ; cong = λ (ε , sε , h) → ε , sε , Nonexpansive.preserves f h }
    ; identity     = λ {A} → ∼Small-refl A
    ; homomorphism = λ {_} {_} {Z} → ∼Small-refl Z
    ; F-resp-≈     = λ {_} {B} e {x} → ε₀ , small-ε₀ , e x
    }
