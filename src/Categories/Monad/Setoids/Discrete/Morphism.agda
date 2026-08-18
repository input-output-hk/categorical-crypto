{-# OPTIONS --safe --without-K #-}

-- A morphism of monads on `Setoids`, viewed elementwise at the discrete
-- setoids; see `Categories.Monad.Setoids.Discrete` for the object side.

open import Level

open import Categories.Category.Instance.Setoids
open import Categories.Monad.Construction.Kleisli
open import Categories.Monad.Construction.Kleisli.Ext
open import Categories.Monad.Relative using () renaming (Monad to RMonad)
import Categories.Monad.Setoids.Discrete as Discrete

open import Function.Base
open import Function.Bundles
open import Function.Bundles.Ext
open import Relation.Binary.PropositionalEquality.Properties using () renaming (setoid to ≡-setoid)

module Categories.Monad.Setoids.Discrete.Morphism {ℓ}
  (K K′ : KleisliTriple (Setoids ℓ ℓ)) (Θᶜ : KleisliTriple⇒ (Setoids ℓ ℓ) K K′) where

open Discrete K

private
  module K′ = RMonad K′
  module Θ = Morphism (Setoids ℓ ℓ) K K′ Θᶜ

  variable A B : Set ℓ

module N = Discrete K′

open N using () renaming (M to Mᴺ; _≈ᴹ_ to _≈ᴺ_) public

θ : M A → Mᴺ A
θ {A} = Θ.θ {≡-setoid A} ⟨$⟩_

θ-cong : {x y : M A} → x ≈ᴹ y → θ x ≈ᴺ θ y
θ-cong {A} = Func.cong (Θ.θ {≡-setoid A})

θ-return : (a : A) → θ (return a) ≈ᴺ N.return a
θ-return {A} _ = Θ.θ-unit {≡-setoid A}

-- `θ-extend` lands in `extend` of the composite setoid map; that agrees with
-- `θ ∘ k`'s own pointwise, not as a record.
θ-bind : (m : M A) (k : A → M B) → θ (m >>= k) ≈ᴺ (θ m N.>>= (θ ∘ k))
θ-bind {A} {B} _ k =
  N.≈ᴹ.trans (Θ.θ-extend (discreteFunc k)) (K′.extend-≈ {h = discreteFunc (θ ∘ k)} N.≈ᴹ.refl)

θ-<$>ᴹ : (h : A → B) (m : M A) → θ (h <$>ᴹ m) ≈ᴺ (h N.<$>ᴹ θ m)
θ-<$>ᴹ h m = N.≈ᴹ.trans (θ-bind m _) (N.>>=-cong-f λ _ → θ-return _)
