{-# OPTIONS --safe --without-K #-}

-- SPIKE: `Rels` satisfies the interface-tensor hypothesis after all.
--
-- The prediction was that specializing the base to "finite products and
-- coproducts" drops `Rels`, because there the finite products *are* the
-- coproducts (`⊎` is a biproduct) while state pairing wants the *multiplicative*
-- product `×`.  That is right for the reading where the state tensor is the
-- base's cartesian product.  But the machine layer only ever uses the state
-- tensor as a symmetric *monoidal* structure, and `Spike.MonoidalDistributive`
-- asks for exactly that, plus a cocartesian `+`, plus a distributor — under
-- which `Rels` still qualifies: `⊗ = ×` (upstream `Rels-Monoidal`, the set
-- product) and `+ = ⊎` (upstream `Rels-Cocartesian`).
--
-- So the specialization does not cost the relational instance.  What it costs is
-- only the *cartesian* reading of the base.

open import Categories.Category.Instance.Rels using (Rels)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Instance.Rels using (Rels-Monoidal; Rels-Symmetric; Rels-Cocartesian)

open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (0ℓ; Lift; lift) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.SFunM.Spike.MonoidalDistributive

module CategoricalCrypto.SFunM.Spike.Instance.RelDist where

𝒱 : SymmetricMonoidalCategory (lsuc 0ℓ) (lsuc 0ℓ) 0ℓ
𝒱 = record { U = Rels 0ℓ 0ℓ ; monoidal = Rels-Monoidal ; symmetric = Rels-Symmetric }

-- The distributor's inverse: the graph of the set-level bijection
-- `X × (A ⊎ B) → (X × A) ⊎ (X × B)`.  A graph of a bijection is invertible in
-- `Rels`, which is the whole content of the instance.
δ⁻¹ : {X A B : Set 0ℓ} → X × (A ⊎ B) → (X × A) ⊎ (X × B) → Set 0ℓ
δ⁻¹ (x , inj₁ a) (inj₁ (y , a′)) = Lift 0ℓ (x ≡ y) × Lift 0ℓ (a ≡ a′)
δ⁻¹ (x , inj₁ _) (inj₂ _)        = ⊥
δ⁻¹ (x , inj₂ _) (inj₁ _)        = ⊥
δ⁻¹ (x , inj₂ b) (inj₂ (y , b′)) = Lift 0ℓ (x ≡ y) × Lift 0ℓ (b ≡ b′)

Rels-MonoidalDistributive : MonoidalDistributive 𝒱
Rels-MonoidalDistributive = record
  { cocartesian       = Rels-Cocartesian
  ; distributeˡ-isIso = record
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
