{-# OPTIONS --safe --without-K #-}

-- The generic machine layer at concrete monads, and what taking the possibility
-- monad as a monad on `Setoids` buys: the endofunctor, the monad, the graded
-- monad, and a graded monad morphism out of `Maybe`.

open import categorical-crypto.Prelude hiding (Functor)

open import Categories.Category.Core
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor using (Functor; Endofunctor) renaming (id to idF)
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties
import Categories.Monad as C
open import Categories.Monad.Construction.Kleisli
open import Categories.Monad.Construction.Kleisli.Ext
open import Categories.Monad.Graded
open import Categories.Monad.Graded.Morphism
open import Categories.Monad.Graded.Trivial
open import Categories.Monad.Graded.Uncurried
open import Categories.Monad.Relative using (RMonad⇒Functor)
open import Categories.Monad.Setoids.Maybe

open import Data.List.Base using (fromMaybe)
open import Data.List.Properties
import Data.Maybe.Relation.Binary.Pointwise as Pw

open import Function.Bundles
open import Relation.Binary.Bundles using (Setoid)

import CategoricalCrypto.SFunM as SFun
import CategoricalCrypto.SFunM.Monoidal as SFunMonoidal
import CategoricalCrypto.SFunM.Morphism as SFunMorphism
import CategoricalCrypto.SFunM.Properties as SFunProperties
open import ProbabilisticLogic.Distribution.Possibility

module CategoricalCrypto.SFunM.Test.Possibility where

𝒫ᵏ : KleisliTriple (Setoids 0ℓ 0ℓ)
𝒫ᵏ = 𝒫-KleisliTriple

Maybeᵏ : KleisliTriple (Setoids 0ℓ 0ℓ)
Maybeᵏ = Maybe-KleisliTriple

open SFun 𝒫ᵏ
open Laws 𝒫-commutative
open SFunMonoidal 𝒫ᵏ 𝒫-commutative
open SFunProperties 𝒫ᵏ

_ : Category _ _ _
_ = SFunᵉ-Category

_ : Monoidal SFunᵉ-Category
_ = SFunᵉ-Monoidal

_ : Symmetric SFunᵉ-Monoidal
_ = SFunᵉ-Symmetric

_ : MonoidalCategory _ _ _
_ = SFunᵉ-MonoidalCategory

_ : eval (statelessᵉ not) (true ∷ false ∷ []) ≡ (false ∷ true ∷ []) ∷ []
_ = refl

_ : eval (statelessᵉ not ⊗ᵉ statelessᵉ id)
         (inj₁ true ∷ inj₂ true ∷ inj₁ false ∷ [])
  ≡ (inj₁ false ∷ inj₂ true ∷ inj₁ true ∷ []) ∷ []
_ = refl

------------------------------------------------------------------------
-- Abstracting a partial machine to a possibilistic one

fromMaybeᵏ : KleisliTriple⇒ (Setoids 0ℓ 0ℓ) Maybeᵏ 𝒫ᵏ
fromMaybeᵏ = record
  { θ        = λ {S} → record
      { to   = fromMaybe
      ; cong = λ where
          (Pw.just a≈b) → return-cong𝒫 {S = S} a≈b
          Pw.nothing    → Setoid.refl (𝒫ˢ S)
      }
  ; θ-unit   = λ {S} → Setoid.refl (𝒫ˢ S)
  ; θ-extend = λ {_} {S′} f → λ where
      {nothing} → Setoid.refl (𝒫ˢ S′)
      {just a}  → Setoid.reflexive (𝒫ˢ S′) (sym (++-identityʳ (fromMaybe (f ⟨$⟩ a))))
  }

private
  module Mb  = SFun.Laws Maybeᵏ Maybe-commutative
  module MbM = SFunMonoidal Maybeᵏ Maybe-commutative

open SFunMorphism Maybeᵏ 𝒫ᵏ fromMaybeᵏ Maybe-commutative 𝒫-commutative

_ : Functor Mb.SFunᵉ-Category SFunᵉ-Category
_ = SFunᵉ-map

_ : StrongMonoidalFunctor MbM.SFunᵉ-MonoidalCategory SFunᵉ-MonoidalCategory
_ = SFunᵉ-map-monoidal

------------------------------------------------------------------------
-- The `Setoids` payoffs

_ : Endofunctor (Setoids 0ℓ 0ℓ)
_ = RMonad⇒Functor 𝒫ᵏ

_ : C.Monad (Setoids 0ℓ 0ℓ)
_ = Kleisli⇒Monad (Setoids 0ℓ 0ℓ) 𝒫ᵏ

_ : GradedKleisliTriple (Oneᴹ {0ℓ} {0ℓ} {0ℓ}) (Setoids 0ℓ 0ℓ)
_ = ungraded 𝒫ᵏ

_ : GradedMonad (Oneᴹ {0ℓ} {0ℓ} {0ℓ}) (Setoids 0ℓ 0ℓ)
_ = GradedKleisliTriple⇒GradedMonad (ungraded 𝒫ᵏ)

fromMaybeᵍ : GradedMonadMorphism _ _ idF (idF-Monoidal (Oneᴹ {0ℓ} {0ℓ} {0ℓ}))
fromMaybeᵍ = toMonadMorphism (ungraded Maybeᵏ) (ungraded 𝒫ᵏ) idF (idF-Monoidal Oneᴹ)
                             (ungraded-morphism Maybeᵏ 𝒫ᵏ fromMaybeᵏ)
