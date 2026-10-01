{-# OPTIONS --safe --without-K #-}

-- The possibilistic abstraction of the machine world: `supp⊥` post-composed
-- with every step kernel.  States, interfaces and control flow are untouched,
-- so `SFun-supp` is a strict monoidal functor; a certainly-diverging step
-- becomes the empty set of outcomes.  It does NOT preserve
-- indistinguishability (`RationalDist.Support`'s `pad-not-perfect` and
-- `close-supp-differs`).

module CategoricalCrypto.SFunPossibility where

open import categorical-crypto.Prelude hiding (Functor)

open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)
open import Categories.Monad.Discrete

open import CategoricalCrypto.SFunPartial
open import ProbabilisticLogic.Distribution.Possibility
open import ProbabilisticLogic.Distribution.RationalDist.Support

import CategoricalCrypto.SFunM as SFunM
import CategoricalCrypto.SFunM.Monoidal as SFunMonoidal
import CategoricalCrypto.SFunM.Morphism as SFunMorphism

private variable A B : Type

Listᴰ : DiscreteMonad 0ℓ
Listᴰ = record
  { elementwise = record
      { ≈ᴹ-setoid       = λ A → record
          { Carrier = List A ; _≈_ = _≈𝒫_ ; isEquivalence = ≈𝒫-isEquivalence }
      ; return          = _∷ []
      ; _>>=_           = λ σ f → concatMap f σ
      ; >>=-cong        = λ {x = σ} {τ} {f} {g} → >>=𝒫-cong {σ = σ} {τ} {f} {g}
      ; >>=-identityˡ-≈ = λ {a = a} {h} → >>=𝒫-identityˡ a h
      ; >>=-identityʳ-≈ = >>=𝒫-identityʳ
      ; >>=-assoc-≈     = λ m {g} {h} → >>=𝒫-assoc m g h
      }
  ; >>=-comm = λ {x = σ} {τ} → >>=𝒫-comm σ τ
  }

-- `_≈Mℚ_` mentions only `entries`, so `supp⊥-cong`'s two distributions are not
-- recoverable from the equality proof and are handed to it by name below.
private
  module S = SFunMorphism Dist⊥ᴰ Listᴰ supp⊥ (λ {_ x y} → supp⊥-cong {μ = x} {y})
                          supp⊥-return supp⊥-bind

suppᵉ : SFun⊥ A B → SFunM.SFunᵉ Listᴰ A B
suppᵉ = S.mapᵉ

SFun-supp : Functor SFun⊥-Category (SFunM.SFunᵉ-Category Listᴰ)
SFun-supp = S.SFunᵉ-map

SFun-supp-monoidal : StrongMonoidalFunctor SFun⊥-MonoidalCategory
                                           (SFunMonoidal.SFunᵉ-MonoidalCategory Listᴰ)
SFun-supp-monoidal = S.SFunᵉ-map-monoidal
