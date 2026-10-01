{-# OPTIONS --safe --without-K #-}

-- PARTIAL probabilistic stateful functions: `SFunM` at the sub-probability
-- monad `Dist⊥ = Dist-ℚ ∘ Maybe`.

open import categorical-crypto.Prelude hiding (Stable)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Monad.Discrete

open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid

import CategoricalCrypto.SFunM as SFunM
import CategoricalCrypto.SFunM.Monoidal as SFunMonoidal

module CategoricalCrypto.SFunPartial where

-- ONE named monad on both sides of every statement below: checking a
-- `Monoidal C` against a `Monoidal C′` with `C`, `C′` *different definitions*
-- of the same category makes Agda compare the two record types field by field,
-- which at `Dist⊥` costs >120 s instead of <1 s.
Dist⊥ᴰ : DiscreteMonad 0ℓ
Dist⊥ᴰ = record
  { elementwise = record
      { ≈ᴹ-setoid       = λ A → Mℚ-setoid (Maybe A)
      ; return          = return⊥
      ; _>>=_           = _>>=⊥_
      ; >>=-cong        = λ {x = μ} {ν} {f} {g} → >>=⊥-cong {μ = μ} {ν} {f} {g}
      ; >>=-identityˡ-≈ = λ {a = a} {h} → >>=⊥-identityˡ a h
      ; >>=-identityʳ-≈ = >>=⊥-identityʳ
      ; >>=-assoc-≈     = λ m {g} {h} → >>=⊥-assoc m g h
      }
  ; >>=-comm = λ {x = x} {y} → >>=⊥-comm x y
  }

SFun⊥ : Type → Type → Type₁
SFun⊥ = SFunM.SFunᵉ Dist⊥ᴰ

SFun⊥-Category : Category _ _ _
SFun⊥-Category = SFunM.SFunᵉ-Category Dist⊥ᴰ

SFun⊥-MonoidalCategory : MonoidalCategory _ _ _
SFun⊥-MonoidalCategory = SFunMonoidal.SFunᵉ-MonoidalCategory Dist⊥ᴰ

SFun⊥-Symmetric : Symmetric (SFunMonoidal.SFunᵉ-Monoidal Dist⊥ᴰ)
SFun⊥-Symmetric = SFunMonoidal.SFunᵉ-Symmetric Dist⊥ᴰ
