{-# OPTIONS --safe --without-K #-}

-- The PARTIAL rational distribution monad `Dist⊥ A = Dist-ℚ (Maybe A)`: total
-- mass stays 1 and `nothing` is an explicit divergence/deadlock sink, so `Dist⊥`
-- represents finitely-supported SUB-probability computations.

open import categorical-crypto.Prelude

open import Class.Core
open import Class.Monad

open import Data.Rational as ℚ
open import Data.Rational.Properties

open import Relation.Binary

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Setoid

module ProbabilisticLogic.Distribution.RationalDist.Partial where

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″

private
  module Eq {ℓ} {A : Type ℓ} = IsEquivalence (≈Mℚ-isEquivalence {A = A})

------------------------------------------------------------------------
-- The partial monad.

Dist⊥ : Type ℓ → Type ℓ
Dist⊥ A = Dist-ℚ (Maybe A)

return⊥ : A → Dist⊥ A
return⊥ a = return-ℚ (just a)

kmaybe : (A → Dist⊥ B) → Maybe A → Dist⊥ B
kmaybe f (just a) = f a
kmaybe f nothing  = return-ℚ nothing

infixl 1 _>>=⊥_
_>>=⊥_ : Dist⊥ A → (A → Dist⊥ B) → Dist⊥ B
μ >>=⊥ f = μ >>=ᴹ kmaybe f

------------------------------------------------------------------------
-- Monad + setoid-monad structure.

>>=⊥-cong : {μ ν : Dist⊥ A} {f g : A → Dist⊥ B}
          → μ ≈Mℚ ν → (∀ a → f a ≈Mℚ g a) → (μ >>=⊥ f) ≈Mℚ (ν >>=⊥ g)
>>=⊥-cong {μ = μ} {ν} {f} {g} μ≈ν f≈g =
  >>=ᴹ-cong {μ = μ} {ν} {kmaybe f} {kmaybe g} μ≈ν kpt
  where
    kpt : ∀ ma → kmaybe f ma ≈Mℚ kmaybe g ma
    kpt (just a) = f≈g a
    kpt nothing  = (λ P → refl)

>>=⊥-identityˡ : (a : A) (h : A → Dist⊥ B) → (return⊥ a >>=⊥ h) ≈Mℚ h a
>>=⊥-identityˡ a h = >>=ᴹ-identityˡ (just a) (kmaybe h)

>>=⊥-congʳ : (f : A → Dist⊥ B) (μ ν : Dist⊥ A) → μ ≈Mℚ ν → (μ >>=⊥ f) ≈Mℚ (ν >>=⊥ f)
>>=⊥-congʳ f μ ν μ≈ν = >>=⊥-cong {μ = μ} {ν} {f} {f} μ≈ν (λ a → Eq.refl {x = f a})

Dmap⊥ : (A → B) → Dist⊥ A → Dist⊥ B
Dmap⊥ f μ = μ >>=⊥ (return⊥ ∘ f)
