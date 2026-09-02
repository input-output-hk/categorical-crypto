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
  (M N : KleisliTriple (Setoids ℓ ℓ)) (Θ : KleisliTriple⇒ (Setoids ℓ ℓ) M N) where

module ℳ = Discrete M
module 𝒩 = Discrete N

private
  module Nᴿ = RMonad N
  module Θ = KleisliTriple⇒ Θ

  variable A B : Set ℓ

θ : ℳ.M A → 𝒩.M A
θ {A} = Θ.θ {≡-setoid A} ⟨$⟩_

θ-cong : {x y : ℳ.M A} → x ℳ.≈ᴹ y → θ x 𝒩.≈ᴹ θ y
θ-cong {A} = Func.cong (Θ.θ {≡-setoid A})

θ-return : (a : A) → θ (ℳ.return a) 𝒩.≈ᴹ 𝒩.return a
θ-return {A} _ = Θ.θ-unit {≡-setoid A}

-- `θ-extend` lands in `extend` of the composite setoid map; that agrees with
-- `θ ∘ k`'s own pointwise, not as a record.
θ-bind : (m : ℳ.M A) (k : A → ℳ.M B) → θ (m ℳ.>>= k) 𝒩.≈ᴹ (θ m 𝒩.>>= (θ ∘ k))
θ-bind _ k =
  𝒩.≈ᴹ.trans (Θ.θ-extend (discreteFunc k)) (Nᴿ.extend-≈ {h = discreteFunc (θ ∘ k)} 𝒩.≈ᴹ.refl)

θ-<$>ᴹ : (h : A → B) (m : ℳ.M A) → θ (h ℳ.<$>ᴹ m) 𝒩.≈ᴹ (h 𝒩.<$>ᴹ θ m)
θ-<$>ᴹ h m = 𝒩.≈ᴹ.trans (θ-bind m _) (𝒩.>>=-cong-f λ _ → θ-return _)
