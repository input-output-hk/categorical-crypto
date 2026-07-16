{-# OPTIONS --safe --without-K #-}

-- The kernel congruence of a functor F : C → D: parallel C-morphisms f, g are
-- identified iff F₁ f ≈ F₁ g in D.

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Properties

module Categories.KernelCongruence
  {oc ℓc ec od ℓd ed} (C : Category oc ℓc ec) (D : Category od ℓd ed) (F : Functor C D) where

open import Function
open import Relation.Binary.Bundles
open import Relation.Binary.Structures
import Relation.Binary.Construct.On as On

private
  module C = Category C
  module D = Category D
  variable X Y Z : C.Obj
open Functor F

infix 4 _∼_

_∼_ : C [ X , Y ] → C [ X , Y ] → Set ed
_∼_ = D._≈_ on F₁

∼-isEquivalence : IsEquivalence (_∼_ {X} {Y})
∼-isEquivalence = On.isEquivalence F₁ D.equiv

module ∼ {X Y} = IsEquivalence (∼-isEquivalence {X} {Y})

∼-refl : {f : C [ X , Y ]} → f ∼ f
∼-refl = ∼.refl

∼-sym : {f g : C [ X , Y ]} → f ∼ g → g ∼ f
∼-sym = ∼.sym

∼-trans : {f g h : C [ X , Y ]} → f ∼ g → g ∼ h → f ∼ h
∼-trans = ∼.trans

∼-setoid : ∀ X Y → Setoid ℓc ed
∼-setoid X Y = On.setoid (D.hom-setoid) (F₁ {X} {Y})

≈⇒∼ : {f g : C [ X , Y ]} → C [ f ≈ g ] → f ∼ g
≈⇒∼ = F-resp-≈

∼⇒≈ : Faithful F → {f g : C [ X , Y ]} → f ∼ g → C [ f ≈ g ]
∼⇒≈ faithful = faithful

∼-congˡ : (h : C [ Y , Z ]) {f g : C [ X , Y ]} → f ∼ g → (h C.∘ f) ∼ (h C.∘ g)
∼-congˡ h {f} {g} p = begin
  F₁ (h C.∘ f)     ≈⟨ homomorphism ⟩
  F₁ h D.∘ F₁ f    ≈⟨ D.∘-resp-≈ʳ p ⟩
  F₁ h D.∘ F₁ g    ≈⟨ homomorphism ⟨
  F₁ (h C.∘ g)     ∎
  where open D.HomReasoning

∼-congʳ : (h : C [ X , Y ]) {f g : C [ Y , Z ]} → f ∼ g → (f C.∘ h) ∼ (g C.∘ h)
∼-congʳ h {f} {g} p = begin
  F₁ (f C.∘ h)     ≈⟨ homomorphism ⟩
  F₁ f D.∘ F₁ h    ≈⟨ D.∘-resp-≈ˡ p ⟩
  F₁ g D.∘ F₁ h    ≈⟨ homomorphism ⟨
  F₁ (g C.∘ h)     ∎
  where open D.HomReasoning
