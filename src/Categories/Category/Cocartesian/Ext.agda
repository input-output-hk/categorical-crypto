{-# OPTIONS --safe --without-K #-}

-- The coproduct associator and braiding on the injections.  Upstream builds
-- `+-monoidal` by dualizing `-×-`, so its associator is a nest of `[_,_]`s and
-- each equation is an `inject₁`/`inject₂` chain.

open import Categories.Category.Cocartesian
open import Categories.Category.Cocartesian.Monoidal
open import Categories.Category.Core
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
import Categories.Category.Monoidal.Braided.Properties as BP

module Categories.Category.Cocartesian.Ext
  {o ℓ e} (C : Category o ℓ e) (cocart : Cocartesian C) where

open Category C
open Cocartesian cocart
open HomReasoning

open import Categories.Morphism.Reasoning C

private variable A B D : Obj

module ⊕ = Monoidal (CocartesianMonoidal.+-monoidal cocart)

+-unique₂ : {Y : Obj} {u v : A + B ⇒ Y} → u ∘ i₁ ≈ v ∘ i₁ → u ∘ i₂ ≈ v ∘ i₂ → u ≈ v
+-unique₂ e₁ e₂ = ⟺ +-g-η ○ []-cong₂ e₁ e₂ ○ +-g-η

α+⇒-i₁i₁ : +-assocˡ ∘ i₁ {A + B} {D} ∘ i₁ {A} ≈ i₁
α+⇒-i₁i₁ = pullˡ inject₁ ○ inject₁

α+⇒-i₁i₂ : +-assocˡ {A} ∘ i₁ {A + B} {D} ∘ i₂ {A} ≈ i₂ ∘ i₁
α+⇒-i₁i₂ = pullˡ inject₁ ○ inject₂

α+⇒-i₂ : +-assocˡ {A} {B} {D} ∘ i₂ ≈ i₂ ∘ i₂
α+⇒-i₂ = inject₂

α+⇐-i₁ : +-assocʳ {A} {B} {D} ∘ i₁ ≈ i₁ ∘ i₁
α+⇐-i₁ = inject₁

α+⇐-i₂i₁ : +-assocʳ {A} {B} ∘ i₂ {A} ∘ i₁ {B} {D} ≈ i₁ ∘ i₂
α+⇐-i₂i₁ = pullˡ inject₂ ○ inject₁

α+⇐-i₂i₂ : +-assocʳ ∘ i₂ {A} ∘ i₂ {B} {D} ≈ i₂
α+⇐-i₂i₂ = pullˡ inject₂ ○ inject₂

α+⇐-i₂ : +-assocʳ {A} {B} {D} ∘ i₂ ≈ i₂ +₁ id
α+⇐-i₂ = inject₂ ○ []-cong₂ Equiv.refl (⟺ identityʳ)

module _ (β : Symmetric (CocartesianMonoidal.+-monoidal cocart)) where
  open Symmetric β using (braided; commutative)
  open BP.Shorthands braided

  braiding-i₁ : σ⇒ {A} {B} ∘ i₁ ≈ i₂
  braiding-i₁ {A} {B} = refl⟩∘⟨ ⟺ (+₁∘i₁ ○ identityʳ)
    ○ pullˡ (σ⇒-comm {f = id} {g = ¡}) ○ assoc
    ○ refl⟩∘⟨ (switch-fromtoˡ ⊕.unitorˡ (pullˡ (BP.braiding-coherence braided) ○ inject₁) ○ identityʳ)
    ○ +₁∘i₂ ○ identityʳ

  braiding-swap : σ⇒ {A} {B} ≈ +-swap
  braiding-swap = +-unique₂ (braiding-i₁ ○ ⟺ inject₁)
    (refl⟩∘⟨ ⟺ braiding-i₁ ○ cancelˡ commutative ○ ⟺ inject₂)
