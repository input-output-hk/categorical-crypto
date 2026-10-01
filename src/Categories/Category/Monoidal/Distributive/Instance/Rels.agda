{-# OPTIONS --safe --without-K #-}

-- `Rels` is monoidal-distributive for the set product `×` (`Rels-Monoidal`) over the
-- coproduct `⊎` (`Rels-Cocartesian`), even though its categorical product is also `⊎`.

open import Categories.Category.Instance.Rels
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Distributive
open import Categories.Category.Monoidal.Instance.Rels

open import Data.Empty.Polymorphic
open import Data.Product
open import Data.Sum
open import Level
open import Relation.Binary.PropositionalEquality

module Categories.Category.Monoidal.Distributive.Instance.Rels {o ℓ : Level} where

Rels-SymmetricMonoidal : SymmetricMonoidalCategory (suc o) (suc (o ⊔ ℓ)) (o ⊔ ℓ)
Rels-SymmetricMonoidal = record { U = Rels o ℓ ; monoidal = Rels-Monoidal ; symmetric = Rels-Symmetric }

δ⁻¹ : {X A B : Set o} → X × (A ⊎ B) → (X × A) ⊎ (X × B) → Set (o ⊔ ℓ)
δ⁻¹ (x , inj₁ a) (inj₁ (y , a′)) = Lift ℓ (x ≡ y) × Lift ℓ (a ≡ a′)
δ⁻¹ (x , inj₁ _) (inj₂ _)        = ⊥
δ⁻¹ (x , inj₂ _) (inj₁ _)        = ⊥
δ⁻¹ (x , inj₂ b) (inj₂ (y , b′)) = Lift ℓ (x ≡ y) × Lift ℓ (b ≡ b′)

Rels-MonoidalDistributive : MonoidalDistributive Rels-SymmetricMonoidal
Rels-MonoidalDistributive = record
  { cocartesian = Rels-Cocartesian
  ; isIsoˡ      = record
      { inv = δ⁻¹
      ; iso = record
          { isoˡ =
              (λ { {inj₁ (x , a)} {inj₁ (y , a′)}
                     ((z , inj₁ c) , (lift refl , lift refl) , lift refl , lift refl) → lift refl
                 ; {inj₂ (x , b)} {inj₂ (y , b′)}
                     ((z , inj₂ c) , (lift refl , lift refl) , lift refl , lift refl) → lift refl })
            , (λ { {inj₁ (x , a)} {_} (lift refl) →
                     (x , inj₁ a) , (lift refl , lift refl) , lift refl , lift refl
                 ; {inj₂ (x , b)} {_} (lift refl) →
                     (x , inj₂ b) , (lift refl , lift refl) , lift refl , lift refl })
          ; isoʳ =
              (λ { {x , inj₁ a} {y , inj₁ a′}
                     (inj₁ (z , c) , (lift refl , lift refl) , lift refl , lift refl) → lift refl
                 ; {x , inj₂ b} {y , inj₂ b′}
                     (inj₂ (z , c) , (lift refl , lift refl) , lift refl , lift refl) → lift refl })
            , (λ { {x , inj₁ a} {_} (lift refl) →
                     inj₁ (x , a) , (lift refl , lift refl) , lift refl , lift refl
                 ; {x , inj₂ b} {_} (lift refl) →
                     inj₂ (x , b) , (lift refl , lift refl) , lift refl , lift refl })
          }
      }
  }
