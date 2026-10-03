{-# OPTIONS --safe --without-K #-}

-- `Rels` is monoidal-distributive for the set product `×` (`Rels-Monoidal`) over the
-- coproduct `⊎` (`Rels-Cocartesian`), even though its categorical product is also `⊎`.

open import Categories.Category.Instance.Rels
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Distributive
open import Categories.Category.Monoidal.Instance.Rels

open import Data.Product
open import Data.Product.Algebra
open import Data.Sum
open import Function.Bundles using (Inverse)
open import Level
open import Relation.Binary.PropositionalEquality

module Categories.Category.Monoidal.Distributive.Instance.Rels {o ℓ : Level} where

Rels-SymmetricMonoidal : SymmetricMonoidalCategory (suc o) (suc (o ⊔ ℓ)) (o ⊔ ℓ)
Rels-SymmetricMonoidal = record { U = Rels o ℓ ; monoidal = Rels-Monoidal ; symmetric = Rels-Symmetric }

δ⁻¹ : {X A B : Set o} → X × (A ⊎ B) → (X × A) ⊎ (X × B) → Set (o ⊔ ℓ)
δ⁻¹ {X} {A} {B} p q = Lift ℓ (Inverse.to (×-distribˡ-⊎ o X A B) p ≡ q)

Rels-MonoidalDistributive : MonoidalDistributive Rels-SymmetricMonoidal
Rels-MonoidalDistributive = record
  { cocartesian = Rels-Cocartesian
  ; isIsoˡ      = record
      { inv = δ⁻¹
      ; iso = record
          { isoˡ =
              (λ { {inj₁ _} ((_ , inj₁ _) , (lift refl , lift refl) , lift refl) → lift refl
                 ; {inj₂ _} ((_ , inj₂ _) , (lift refl , lift refl) , lift refl) → lift refl })
            , (λ { {inj₁ (x , a)} (lift refl) → (x , inj₁ a) , (lift refl , lift refl) , lift refl
                 ; {inj₂ (x , b)} (lift refl) → (x , inj₂ b) , (lift refl , lift refl) , lift refl })
          ; isoʳ =
              (λ { {_ , inj₁ _} {_ , inj₁ _} (_ , lift refl , lift refl , lift refl) → lift refl
                 ; {_ , inj₂ _} {_ , inj₂ _} (_ , lift refl , lift refl , lift refl) → lift refl })
            , (λ { {x , inj₁ a} (lift refl) → inj₁ (x , a) , lift refl , lift refl , lift refl
                 ; {x , inj₂ b} (lift refl) → inj₂ (x , b) , lift refl , lift refl , lift refl })
          }
      }
  }
