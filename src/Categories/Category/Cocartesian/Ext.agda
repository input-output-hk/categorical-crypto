{-# OPTIONS --safe --without-K #-}

-- The coproduct associator and braiding, read off on the injections.  Upstream
-- builds `+-monoidal` by dualizing `-×-`, so its associator is a nest of
-- `[_,_]`s and every equation below is `inject₁`/`inject₂`; the ⊕-side
-- bookkeeping of the machine layer's trace laws is exactly these facts.

open import Categories.Category.Core using (Category)
open import Categories.Category.Cocartesian using (Cocartesian)

import Categories.Category.Cocartesian as Cocart

module Categories.Category.Cocartesian.Ext
  {o ℓ e} (C : Category o ℓ e) (cocart : Cocartesian C) where

open Category C
open Cocartesian cocart
open Equiv
open HomReasoning

open import Categories.Morphism.Reasoning C

private variable A B D : Obj

module ⊕ = Cocart.CocartesianMonoidal C cocart

+-unique₂ : {Y : Obj} {u v : A + B ⇒ Y} → u ∘ i₁ ≈ v ∘ i₁ → u ∘ i₂ ≈ v ∘ i₂ → u ≈ v
+-unique₂ e₁ e₂ = ⟺ +-g-η ○ []-cong₂ e₁ e₂ ○ +-g-η

+₁-id : id {A} +₁ id {B} ≈ id
+₁-id = ⟺ (+-unique (+₁∘i₁ ○ identityʳ) (+₁∘i₂ ○ identityʳ)) ○ +-η

α+⇒ : (A + B) + D ⇒ A + (B + D)
α+⇒ = ⊕.associator.from

α+⇐ : A + (B + D) ⇒ (A + B) + D
α+⇐ = ⊕.associator.to

α+⇒-i₁i₁ : α+⇒ {A} {B} {D} ∘ i₁ {A + B} {D} ∘ i₁ {A} {B} ≈ i₁
α+⇒-i₁i₁ = pullˡ inject₁ ○ inject₁

α+⇒-i₁i₂ : α+⇒ {A} {B} {D} ∘ i₁ {A + B} {D} ∘ i₂ {A} {B} ≈ i₂ ∘ i₁
α+⇒-i₁i₂ = pullˡ inject₁ ○ inject₂

α+⇒-i₂ : α+⇒ {A} {B} {D} ∘ i₂ ≈ i₂ ∘ i₂
α+⇒-i₂ = inject₂

α+⇐-i₁ : α+⇐ {A} {B} {D} ∘ i₁ ≈ i₁ ∘ i₁
α+⇐-i₁ = inject₁

α+⇐-i₂i₁ : α+⇐ {A} {B} {D} ∘ i₂ {A} {B + D} ∘ i₁ {B} {D} ≈ i₁ ∘ i₂
α+⇐-i₂i₁ = pullˡ inject₂ ○ inject₁

α+⇐-i₂i₂ : α+⇐ {A} {B} {D} ∘ i₂ {A} {B + D} ∘ i₂ {B} {D} ≈ i₂
α+⇐-i₂i₂ = pullˡ inject₂ ○ inject₂

-- The form the ⊕-trace's `vanishing₂` and `superposing` consume: entering
-- `A + (B + D)` on the right summand and re-bracketing relabels the exit branch
-- and leaves the loop branch alone.
α+⇐-i₂ : α+⇐ {A} {B} {D} ∘ i₂ ≈ i₂ +₁ id
α+⇐-i₂ = +-unique₂ (assoc ○ α+⇐-i₂i₁ ○ ⟺ +₁∘i₁)
                   (assoc ○ α+⇐-i₂i₂ ○ ⟺ (+₁∘i₂ ○ identityʳ))

+-swap-i₁ : +-swap {A} {B} ∘ i₁ ≈ i₂
+-swap-i₁ = inject₁

+-swap-i₂ : +-swap {A} {B} ∘ i₂ ≈ i₁
+-swap-i₂ = inject₂
