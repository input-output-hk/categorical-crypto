{-# OPTIONS --safe --without-K #-}

-- SPIKE: `Spike.MonoidalDistributive` at a Kleisli category is two gifts.
--
--   * Coproducts lift unconditionally.  `Kl(K)(A + B , C)` *is* `𝒞(A + B , K C)`,
--     so the base's own coproduct universal property at the target `K C` already
--     is the Kleisli one; the only step is that precomposing with `η ∘ iⱼ` is
--     precomposing with `iⱼ`.  No monad law beyond `f * ∘ η ≈ f` is used, and no
--     strength or commutativity at all.
--   * The distributor lifts along `pure = η ∘_`.  The Kleisli tensor of two pure
--     maps is the pure image of the base tensor — `ψ-η` is the whole content —
--     so the Kleisli `distributeˡ` is `η ∘` the base one, and `η ∘_` preserves
--     isos.
--
-- Hence a base `MonoidalDistributive` transports to the Kleisli SMC.  The
-- cartesian bridge at the end says upstream's `Categories.Category.Distributive`
-- already *is* a `MonoidalDistributive`: `-×-`'s `F₁` is `_⁂_`, so the two
-- `distributeˡ` are literally the same term.

open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Construction.Kleisli using (Kleisli; module TripleNotation)
open import Categories.Category.Core using (Category)
open import Categories.Category.Distributive using (Distributive)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Construction.Kleisli using (Kleisli-Monoidal)
open import Categories.Category.Monoidal.Construction.Kleisli.Symmetric using (Kleisli-Symmetric)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Commutative.Properties using (module CommutativeProperties)

open import Data.Product.Base using (_,_)
open import Level using (Level)

import Categories.Category.Cartesian.SymmetricMonoidal as CartesianSymmetric
import Categories.Morphism.Reasoning as MR
import CategoricalCrypto.SFunM.Spike.MonoidalDistributive as MD

module CategoricalCrypto.SFunM.Spike.KleisliDistributive where

private variable o ℓ e : Level

------------------------------------------------------------------------
-- Gift (a): coproducts lift, with no conditions on the monad

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

------------------------------------------------------------------------
-- Gift (b): the distributor lifts along `pure`

module _ {𝒞 : Category o ℓ e} {monoidal : Monoidal 𝒞} (symmetric : Symmetric monoidal)
  (CM : CommutativeMonad (Symmetric.braided symmetric)) where

  open Category 𝒞
  open Equiv
  open HomReasoning
  open MR 𝒞
  open CommutativeMonad CM using (M)
  open CommutativeProperties (Symmetric.braided symmetric) CM using (ψ; ψ-η)
  open Monoidal monoidal using (_⊗₁_; module ⊗)
  open TripleNotation M

  Base-SMC : SymmetricMonoidalCategory o ℓ e
  Base-SMC = record { U = 𝒞 ; monoidal = monoidal ; symmetric = symmetric }

  Kleisli-SMC : SymmetricMonoidalCategory o ℓ e
  Kleisli-SMC = record
    { U         = Kleisli M
    ; monoidal  = Kleisli-Monoidal symmetric CM
    ; symmetric = Kleisli-Symmetric symmetric CM
    }

  module MDᵇ = MD Base-SMC
  module MDᵏ = MD Kleisli-SMC

  -- The Kleisli tensor of two pure maps is the pure image of the base tensor.
  -- This is the law the distributor lifting needs, and `ψ-η` is all of it.
  pure-⊗ : ∀ {X A B} {g : A ⇒ B} → ψ ∘ (η {X} ⊗₁ (η ∘ g)) ≈ η ∘ (id ⊗₁ g)
  pure-⊗ {g = g} = begin
    ψ ∘ (η ⊗₁ (η ∘ g))       ≈˘⟨ refl⟩∘⟨ (⟺ ⊗.homomorphism ○ ⊗.F-resp-≈ (identityʳ , refl)) ⟩
    ψ ∘ (η ⊗₁ η) ∘ (id ⊗₁ g) ≈⟨ pullˡ ψ-η ⟩
    η ∘ (id ⊗₁ g)            ∎

  MonoidalDistributive-Kleisli : MDᵇ.MonoidalDistributive → MDᵏ.MonoidalDistributive
  MonoidalDistributive-Kleisli mdᵇ = record
    { cocartesian       = Cocartesian-Kleisli M cocartesian
    ; distributeˡ-isIso = record
        { inv = η ∘ distributeˡ.inv
        ; iso = record
            { isoˡ = ∘-resp-≈ʳ pure-distributeˡ ○ pullˡ *-identityʳ ○ pullʳ distributeˡ.isoˡ ○ identityʳ
            ; isoʳ = pullˡ *-identityʳ ○ ∘-resp-≈ˡ pure-distributeˡ ○ pullʳ distributeˡ.isoʳ ○ identityʳ
            }
        }
    }
    where
    open MDᵇ.MonoidalDistributive mdᵇ

    pure-distributeˡ : ∀ {X A B}
      → [ ψ ∘ (η ⊗₁ (η ∘ i₁)) , ψ ∘ (η ⊗₁ (η ∘ i₂)) ] ≈ η ∘ distributeˡ {X} {A} {B}
    pure-distributeˡ = []-cong₂ pure-⊗ pure-⊗ ○ ⟺ ∘-distribˡ-[]

------------------------------------------------------------------------
-- The cartesian bridge

module _ {𝒞 : Category o ℓ e} (D : Distributive 𝒞) where
  open Distributive D

  Cartesian-SMC : SymmetricMonoidalCategory o ℓ e
  Cartesian-SMC = record
    { U         = 𝒞
    ; monoidal  = CartesianMonoidal.monoidal cartesian
    ; symmetric = CartesianSymmetric.symmetric 𝒞 cartesian
    }

  MonoidalDistributive-Cartesian : MD.MonoidalDistributive Cartesian-SMC
  MonoidalDistributive-Cartesian = record { cocartesian = cocartesian ; distributeˡ-isIso = isIsoˡ }
