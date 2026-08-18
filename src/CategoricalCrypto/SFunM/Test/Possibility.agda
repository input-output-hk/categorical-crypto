{-# OPTIONS --safe --without-K #-}

-- The generic machine layer at concrete monads.

open import categorical-crypto.Prelude hiding (Functor)

open import Class.Monad.Ext
open import Class.Monad.Ext.Setoid

open import Categories.Category.Core
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal

open import Data.List.Base
open import Data.List.Properties
open import Data.List.Relation.Unary.Any using (Any; here; there)

open import Function.Bundles using (Equivalence)

open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Construct.Always as Always
open import Relation.Binary.Bundles.Ext
open import Relation.Binary.PropositionalEquality.Properties using () renaming (setoid to ≡-setoid)

open import CategoricalCrypto.SFunM
open import CategoricalCrypto.SFunM.Monoidal
open import CategoricalCrypto.SFunM.Morphism
open import CategoricalCrypto.SFunM.Properties
open import ProbabilisticLogic.Distribution.Possibility

module CategoricalCrypto.SFunM.Test.Possibility where

_ : Category _ _ _
_ = SFunᵉ-Category {M = List}

_ : Monoidal (SFunᵉ-Category {M = List})
_ = SFunᵉ-Monoidal

_ : Symmetric (SFunᵉ-Monoidal {M = List})
_ = SFunᵉ-Symmetric

_ : MonoidalCategory _ _ _
_ = SFunᵉ-MonoidalCategory {M = List}

_ : eval {M = List} (statelessᵉ not) (true ∷ false ∷ []) ≡ (false ∷ true ∷ []) ∷ []
_ = refl

_ : eval {M = List} (statelessᵉ not ⊗ᵉ statelessᵉ id)
                    (inj₁ true ∷ inj₂ true ∷ inj₁ false ∷ [])
  ≡ (inj₁ false ∷ inj₂ true ∷ inj₁ true ∷ []) ∷ []
_ = refl

-- Abstracting a partial machine to a possibilistic one, along `fromMaybe : Maybe ⇒ 𝒫`.
-- Its `Maybe` side comes from `FromPropositional`, i.e. from the propositional
-- monad laws `Class.Monad.Instances` already proves.
private
  module Mb = FromPropositional {Maybe}

  instance
    MonadSetoid-Maybe = Mb.Propositional-MonadSetoid
    MonadLawsSetoid-Maybe = Mb.Propositional-MonadLawsSetoid
    CommutativeMonadSetoid-Maybe = Mb.Propositional-CommutativeMonadSetoid

fromMaybeᴹ : MonadMorphismSetoid Maybe List
fromMaybeᴹ = record
  { θ        = fromMaybe
  ; θ-cong   = λ x≡y → 𝒫.reflexive (cong fromMaybe x≡y)
  ; θ-return = λ _ → 𝒫.refl
  ; θ-bind   = λ where
      nothing  _ → 𝒫.refl
      (just a) k → 𝒫.reflexive (sym (++-identityʳ (fromMaybe (k a))))
  }

_ : Functor (SFunᵉ-Category {M = Maybe}) (SFunᵉ-Category {M = List})
_ = SFunᵉ-map fromMaybeᴹ

_ : StrongMonoidalFunctor (SFunᵉ-MonoidalCategory {M = Maybe})
                          (SFunᵉ-MonoidalCategory {M = List})
_ = SFunᵉ-map-monoidal fromMaybeᴹ

------------------------------------------------------------------------
-- The gap the setoid index closes
------------------------------------------------------------------------

private
  -- The one-point setoid on `Bool`: `const true` and `const false` are the same
  -- map into it.
  Bool⋆ : Setoid 0ℓ 0ℓ
  Bool⋆ = Always.setoid Bool 0ℓ

-- Carrier-indexed, the two maps' images are separated, and `<$>ᴹ-congˡ`'s
-- premise `const true ≗ const false` is false — so `_≈ᴹ_` has nothing to say.
_ : ¬ ((const true <$>ᴹ (true ∷ [])) ≈ᴹ (const false <$>ᴹ (true ∷ [])))
_ = λ eq → separate (Equivalence.to eq (here refl))
  where
  separate : ¬ Any (true ≡_) (false ∷ [])
  separate (here ())
  separate (there ())

-- Setoid-indexed, `<$>ᴹ-congˢ-f` identifies them: the gap is closed.
_ : (σ : List Bool) → 𝒫ˢ Bool⋆ ⟨ (const true <$>ᴹ σ) ≈ (const false <$>ᴹ σ) ⟩
_ = <$>ᴹ-congˢ-f {S = ≡-setoid Bool} {S′ = Bool⋆} λ _ → _
