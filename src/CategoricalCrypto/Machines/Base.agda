{-# OPTIONS --safe --without-K --guardedness #-}

-- The base category the machine layer is meant to run over: the Kleisli
-- category of the probabilistic delay monad at discrete objects, symmetric
-- monoidal and distributive.
--
-- Objects are types and homs are `A → Dₚ B` up to `_≈ₚ_`.  Everything the
-- construction needs of the monad is the eight elementwise laws of
-- `DiscreteMonad`, commutativity included — which is what makes the Kleisli
-- category symmetric monoidal, and is the only place `Dₚ`'s Fubini identity is
-- spent.

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Pure using (PureSub)
open import Categories.Monad.Discrete using (DiscreteMonad)
import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Kleisli.Discrete.Distributive as KDD
import Categories.Category.Kleisli.Discrete.Pure as KDP
import Categories.Category.Monoidal.Distributive as MD

open import Data.Product.Base using (_,_)
open import Level using (Level; suc)
open import Relation.Binary.Bundles using (Setoid)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Commutative using (>>=ₚ-comm)

module CategoricalCrypto.Machines.Base where

private variable ℓ : Level

Dₚ-setoid : Set ℓ → Setoid ℓ ℓ
Dₚ-setoid A = record
  { Carrier = Dₚ A
  ; _≈_ = _≈ₚ_
  ; isEquivalence = record
    { refl  = λ {d} → ≈ₚ-refl d
    ; sym   = λ {d} {e} → ≈ₚ-sym d e
    ; trans = λ {d} {e} {h} → ≈ₚ-trans d e h
    }
  }

Dₚ-DiscreteMonad : DiscreteMonad ℓ
Dₚ-DiscreteMonad = record
  { ≈ᴹ-setoid       = Dₚ-setoid
  ; return          = returnₚ
  ; _>>=_           = _>>=ₚ_
  ; >>=-cong        = λ {_} {_} {x} {y} {f} {g} → >>=ₚ-cong x y f g
  ; >>=-identityˡ-≈ = λ {_} {_} {a} {h} → >>=ₚ-identityˡ a h
  ; >>=-identityʳ-≈ = >>=ₚ-identityʳ
  ; >>=-assoc-≈     = λ m {g} {h} → >>=ₚ-assoc m g h
  ; >>=-comm        = λ {_} {_} {x} {y} → >>=ₚ-comm x y
  }

𝒱ₚ : (ℓ : Level) → SymmetricMonoidalCategory (suc ℓ) ℓ ℓ
𝒱ₚ ℓ = KD.Klᴹ-SymmetricMonoidal (Dₚ-DiscreteMonad {ℓ})

distₚ : (ℓ : Level) → MD.MonoidalDistributive (𝒱ₚ ℓ)
distₚ ℓ = KDD.MonoidalDistributiveᵏ (Dₚ-DiscreteMonad {ℓ})

-- The pure state maps: `iterₚ` transfers along these and no others.
𝒫ₚ : (ℓ : Level) → PureSub (𝒱ₚ ℓ)
𝒫ₚ ℓ = KDP.PureSubᵏ (Dₚ-DiscreteMonad {ℓ})
