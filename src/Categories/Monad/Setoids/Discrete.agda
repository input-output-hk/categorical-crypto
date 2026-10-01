{-# OPTIONS --safe --without-K #-}

-- The `Categories.Monad.Discrete` vocabulary read off a `KleisliTriple (Setoids
-- ℓ ℓ)` at the discrete setoids `≡-setoid A`.

open import Categories.Category.Instance.Setoids
open import Categories.Monad.Construction.Kleisli
open import Categories.Monad.Discrete
open import Categories.Monad.Relative using () renaming (Monad to RMonad)

open import Function.Bundles
open import Function.Bundles.Ext
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality.Properties using () renaming (setoid to ≡-setoid)

module Categories.Monad.Setoids.Discrete {ℓ} (K : KleisliTriple (Setoids ℓ ℓ)) where

private module K = RMonad K

elementwise : Elementwise ℓ
elementwise = record
  { ≈ᴹ-setoid       = λ A → K.F₀ (≡-setoid A)
  ; return          = K.unit ⟨$⟩_
  ; _>>=_           = λ x f → K.extend (discreteFunc f) ⟨$⟩ x
  ; >>=-cong        = λ {f = f} x≈y f≈g →
      Setoid.trans (K.F₀ _) (Func.cong (K.extend (discreteFunc f)) x≈y) (K.extend-≈ λ {a} → f≈g a)
  ; >>=-identityˡ-≈ = K.identityʳ
  ; >>=-identityʳ-≈ = λ _ → Setoid.trans (K.F₀ _) (K.extend-≈ (Setoid.refl (K.F₀ _))) K.identityˡ
  ; >>=-assoc-≈     = λ _ → Setoid.trans (K.F₀ _) K.sym-assoc (K.extend-≈ (Setoid.refl (K.F₀ _)))
  }

open Elementwise elementwise public hiding (module Comm)
