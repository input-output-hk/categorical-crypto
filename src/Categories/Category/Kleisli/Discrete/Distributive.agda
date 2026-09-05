{-# OPTIONS --safe --without-K #-}

-- `Klᴹ` is monoidal distributive, with `_⊎_` for the coproduct.  Both halves are
-- one-liners at this base because everything is elementwise: a Kleisli hom out
-- of `A ⊎ B` is a function out of `A ⊎ B`, so the coproduct's uniqueness is two
-- clauses, and the distributor is `return` of the pure
-- `X × (A ⊎ B) ↔ X × A ⊎ X × B` shuffle, so both iso laws are
-- `>>=-identityˡ-≈` chains.  Nothing here touches the monad beyond the left
-- unit law.

open import Categories.Category.Cocartesian
open import Categories.Monad.Discrete

import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Monoidal.Distributive as MD

open import Data.Empty.Polymorphic
open import Data.Product.Algebra
open import Data.Product.Base
open import Data.Sum.Base
open import Function.Bundles

module Categories.Category.Kleisli.Discrete.Distributive {ℓ} (Mo : DiscreteMonad ℓ) where

open DiscreteMonad Mo
open KD Mo
open MD Klᴹ-SymmetricMonoidal

private variable A B X : Set ℓ

-- The pure shuffle the distributor inverts.
undistribute : X × (A ⊎ B) → (X × A) ⊎ (X × B)
undistribute = Inverse.to (×-distribˡ-⊎ ℓ _ _ _)

Cocartesianᵏ : Cocartesian Klᴹ
Cocartesianᵏ = record
  { initial    = record { ⊥ = ⊥ ; ⊥-is-initial = record { ! = ⊥-elim ; !-unique = λ _ → ⊥-elim } }
  ; coproducts = record
      { coproduct = λ {A} {B} → record
          { A+B     = A ⊎ B
          ; i₁      = pureᵏ inj₁
          ; i₂      = pureᵏ inj₂
          ; [_,_]   = [_,_]
          ; inject₁ = λ _ → >>=-identityˡ-≈
          ; inject₂ = λ _ → >>=-identityˡ-≈
          ; unique  = λ h∘i₁≈f h∘i₂≈g → λ where
              (inj₁ a) → ≈ᴹ.trans (≈ᴹ.sym (h∘i₁≈f a)) >>=-identityˡ-≈
              (inj₂ b) → ≈ᴹ.trans (≈ᴹ.sym (h∘i₂≈g b)) >>=-identityˡ-≈
          }
      }
  }

private
  δᵏ : (X × A) ⊎ (X × B) → M (X × (A ⊎ B))
  δᵏ = [ return ⊗ᵏ pureᵏ inj₁ , return ⊗ᵏ pureᵏ inj₂ ]

  δᵏ-isoˡ : (pureᵏ undistribute <=< δᵏ {X} {A} {B}) ≈ᵏ return
  δᵏ-isoˡ (inj₁ (x , a)) = ≈ᴹ.trans (⊗ᵏ-expand return (pureᵏ inj₁) _ (x , a))
    (≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈)
  δᵏ-isoˡ (inj₂ (x , b)) = ≈ᴹ.trans (⊗ᵏ-expand return (pureᵏ inj₂) _ (x , b))
    (≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈)

  δᵏ-isoʳ : (δᵏ <=< pureᵏ (undistribute {X} {A} {B})) ≈ᵏ return
  δᵏ-isoʳ (_ , inj₁ _) = ≈ᴹ.trans >>=-identityˡ-≈ (≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈)
  δᵏ-isoʳ (_ , inj₂ _) = ≈ᴹ.trans >>=-identityˡ-≈ (≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈)

MonoidalDistributiveᵏ : MonoidalDistributive
MonoidalDistributiveᵏ = record
  { cocartesian       = Cocartesianᵏ
  ; distributeˡ-isIso = record
      { inv = pureᵏ undistribute
      ; iso = record { isoˡ = δᵏ-isoˡ ; isoʳ = δᵏ-isoʳ }
      }
  }
