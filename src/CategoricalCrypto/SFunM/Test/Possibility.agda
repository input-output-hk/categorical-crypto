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
  ; θ-return = λ _ _ → refl
  ; θ-bind   = λ where
      nothing  _ _ → refl
      (just a) k → 𝒫.reflexive (sym (++-identityʳ (fromMaybe (k a))))
  }

_ : Functor (SFunᵉ-Category {M = Maybe}) (SFunᵉ-Category {M = List})
_ = SFunᵉ-map fromMaybeᴹ

_ : StrongMonoidalFunctor (SFunᵉ-MonoidalCategory {M = Maybe})
                          (SFunᵉ-MonoidalCategory {M = List})
_ = SFunᵉ-map-monoidal fromMaybeᴹ
