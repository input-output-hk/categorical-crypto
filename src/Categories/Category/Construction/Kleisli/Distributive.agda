{-# OPTIONS --safe --without-K #-}

-- The Kleisli category of a monad inherits coproducts and, for a commutative monad
-- over a monoidal-distributive base, the distributor.

open import Categories.Category.Cocartesian
open import Categories.Category.Construction.Kleisli
open import Categories.Category.Core
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Kleisli
open import Categories.Category.Monoidal.Construction.Kleisli.Symmetric
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative
open import Categories.Monad.Commutative.Properties
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Reasoning as ⊗R
import Categories.Morphism.Reasoning as MR

open import Level

module Categories.Category.Construction.Kleisli.Distributive where

private variable o ℓ e : Level

module _ {𝒞 : Category o ℓ e} (M : Monad 𝒞) where
  open Category 𝒞
  open HomReasoning
  open MR 𝒞
  open TripleNotation M

  Cocartesian-Kleisli : Cocartesian 𝒞 → Cocartesian (Kleisli M)
  Cocartesian-Kleisli cocartesian = record
    { initial    = record { ⊥ = ⊥ ; ⊥-is-initial = record { ! = ¡ ; !-unique = ¡-unique } }
    ; coproducts = record
        { coproduct = λ {A} {B} → record
            { A+B     = A + B
            ; i₁      = η ∘ i₁
            ; i₂      = η ∘ i₂
            ; [_,_]   = [_,_]
            ; inject₁ = pullˡ *-identityʳ ○ inject₁
            ; inject₂ = pullˡ *-identityʳ ○ inject₂
            ; unique  = λ h∘i₁≈f h∘i₂≈g →
                +-unique (⟺ (pullˡ *-identityʳ) ○ h∘i₁≈f) (⟺ (pullˡ *-identityʳ) ○ h∘i₂≈g)
            }
        }
    }
    where open Cocartesian cocartesian

module _ (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (CM : CommutativeMonad (SymmetricMonoidalCategory.braided 𝒱)) where

  open SymmetricMonoidalCategory 𝒱
  open HomReasoning
  open MR U
  open ⊗R monoidal using (split₂ʳ)
  open CommutativeMonad CM
  open CommutativeProperties braided CM
  open TripleNotation M

  Kleisli-SymmetricMonoidal : SymmetricMonoidalCategory o ℓ e
  Kleisli-SymmetricMonoidal = record
    { U         = Kleisli M
    ; monoidal  = Kleisli-Monoidal symmetric CM
    ; symmetric = Kleisli-Symmetric symmetric CM
    }

  pure-⊗ : ∀ {X A B} {g : A ⇒ B} → ψ ∘ (η {X} ⊗₁ (η ∘ g)) ≈ η ∘ (id ⊗₁ g)
  pure-⊗ = (refl⟩∘⟨ split₂ʳ) ○ pullˡ ψ-η

  MonoidalDistributive-Kleisli : MD.MonoidalDistributive 𝒱
                               → MD.MonoidalDistributive Kleisli-SymmetricMonoidal
  MonoidalDistributive-Kleisli dist = record
    { cocartesian = Cocartesian-Kleisli M cocartesian
    ; isIsoˡ      = record
        { inv = η ∘ distributeˡ.inv
        ; iso = record
            { isoˡ = ∘-resp-≈ʳ pure-distributeˡ ○ pullˡ *-identityʳ ○ pullʳ distributeˡ.isoˡ ○ identityʳ
            ; isoʳ = pullˡ *-identityʳ ○ ∘-resp-≈ˡ pure-distributeˡ ○ pullʳ distributeˡ.isoʳ ○ identityʳ
            }
        }
    }
    where
    open MD.MonoidalDistributive dist

    pure-distributeˡ : ∀ {X A B}
      → [ ψ ∘ (η ⊗₁ (η ∘ i₁)) , ψ ∘ (η ⊗₁ (η ∘ i₂)) ] ≈ η ∘ distributeˡ {X} {A} {B}
    pure-distributeˡ = []-cong₂ pure-⊗ pure-⊗ ○ ⟺ ∘-distribˡ-[]
