{-# OPTIONS --safe --without-K #-}

-- The setoid-indexed interface's payoffs at `𝒫` and `Maybe`: the endofunctor on
-- `Setoids`, the monad, the graded monad, and — the construction the note on
-- `MonadMorphismSetoid` says the carrier-indexed equality cannot support — a
-- graded monad morphism.

open import categorical-crypto.Prelude

open import Class.Monad.Ext.Setoid
open import Class.Monad.Ext.Setoid.Graded

open import Categories.Category.Instance.Setoids
open import Categories.Functor using (Endofunctor) renaming (id to idF)
open import Categories.Functor.Monoidal.Properties using (idF-Monoidal)
import Categories.Monad as C
open import Categories.Monad.Graded using (GradedMonad)
open import Categories.Monad.Graded.Trivial using (Oneᴹ)
open import Categories.Monad.Graded.Uncurried using (GradedMonadMorphism)

open import Data.List.Base using (fromMaybe)
open import Data.List.Properties using (++-identityʳ)
import Data.Maybe.Relation.Binary.Pointwise as Pw

open import ProbabilisticLogic.Distribution.Possibility

open import Relation.Binary

module Class.Monad.Ext.Setoid.Test where

open Setoid using (reflexive)

private
  module Mbˢ = PointwiseMaybe

  instance
    SetoidMonad-Maybe = Mbˢ.Pointwise-SetoidMonad
    SetoidMonadLaws-Maybe = Mbˢ.Pointwise-SetoidMonadLaws
    CommutativeSetoidMonad-Maybe = Mbˢ.Pointwise-CommutativeSetoidMonad

fromMaybeˢ : SetoidMonadMorphism Maybe List
fromMaybeˢ = record
  { θ        = fromMaybe
  ; θ-congˢ  = λ {S = S} → λ where
      (Pw.just a≈b) → return-cong𝒫 {S = S} a≈b
      Pw.nothing    → Setoid.refl (𝒫ˢ S)
  ; θ-return = λ {S = S} _ → Setoid.refl (𝒫ˢ S)
  ; θ-bind   = λ {S′ = S′} → λ where
      nothing  _ → Setoid.refl (𝒫ˢ S′)
      (just a) k → reflexive (𝒫ˢ S′) (sym (++-identityʳ (fromMaybe (k a))))
  }

_ : Endofunctor (Setoids 0ℓ 0ℓ)
_ = SetoidMonad-Functor List

_ : C.Monad (Setoids 0ℓ 0ℓ)
_ = SetoidMonad-Monad List

_ : GradedMonad (Oneᴹ {0ℓ} {0ℓ} {0ℓ}) (Setoids 0ℓ 0ℓ)
_ = SetoidMonad-GradedMonad List

-- Naming the two graded monads here would compare two concrete `MonoidalFunctor`
-- records field by field, which does not terminate in reasonable time; they are
-- ascribed where the construction is proved, so leave them to inference.
fromMaybeᵍ : GradedMonadMorphism _ _ idF (idF-Monoidal (Oneᴹ {0ℓ} {0ℓ} {0ℓ}))
fromMaybeᵍ = SetoidMonadMorphism-GradedMonadMorphism {0ℓ} Maybe List fromMaybeˢ
