{-# OPTIONS --safe --without-K #-}

-- The kernel congruence of a functor F : C → D: parallel C-morphisms f, g are
-- identified iff F₁ f ≈ F₁ g in D.

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Properties

module Categories.KernelCongruence
  {oc ℓc ec od ℓd ed} (C : Category oc ℓc ec) (D : Category od ℓd ed) (F : Functor C D) where

open import Relation.Binary.Bundles
open import Relation.Binary.Structures

private
  module C = Category C
  module D = Category D
  variable X Y Z : C.Obj
open Functor F

infix 4 _∼_

record _∼_ {X Y : C.Obj} (f g : C [ X , Y ]) : Set ed where
  constructor mk∼
  no-eta-equality
  field run∼ : D [ F₁ f ≈ F₁ g ]

open _∼_ public

∼-refl : {f : C [ X , Y ]} → f ∼ f
∼-refl = mk∼ D.Equiv.refl

∼-sym : {f g : C [ X , Y ]} → f ∼ g → g ∼ f
∼-sym p = mk∼ (D.Equiv.sym (run∼ p))

∼-trans : {f g h : C [ X , Y ]} → f ∼ g → g ∼ h → f ∼ h
∼-trans p q = mk∼ (D.Equiv.trans (run∼ p) (run∼ q))

∼-isEquivalence : IsEquivalence (_∼_ {X} {Y})
∼-isEquivalence = record { refl = ∼-refl ; sym = ∼-sym ; trans = ∼-trans }

module ∼ {X Y} = IsEquivalence (∼-isEquivalence {X} {Y})

∼-setoid : ∀ X Y → Setoid ℓc ed
∼-setoid X Y = record
  { Carrier = C [ X , Y ] ; _≈_ = _∼_ ; isEquivalence = ∼-isEquivalence }

≈⇒∼ : {f g : C [ X , Y ]} → C [ f ≈ g ] → f ∼ g
≈⇒∼ e = mk∼ (F-resp-≈ e)

∼⇒≈ : Faithful F → {f g : C [ X , Y ]} → f ∼ g → C [ f ≈ g ]
∼⇒≈ faithful p = faithful (run∼ p)

∼-congˡ : (h : C [ Y , Z ]) {f g : C [ X , Y ]} → f ∼ g → (h C.∘ f) ∼ (h C.∘ g)
∼-congˡ h {f} {g} p = mk∼ (begin
  F₁ (h C.∘ f)     ≈⟨ homomorphism ⟩
  F₁ h D.∘ F₁ f    ≈⟨ D.∘-resp-≈ʳ (run∼ p) ⟩
  F₁ h D.∘ F₁ g    ≈⟨ homomorphism ⟨
  F₁ (h C.∘ g)     ∎)
  where open D.HomReasoning

∼-congʳ : (h : C [ X , Y ]) {f g : C [ Y , Z ]} → f ∼ g → (f C.∘ h) ∼ (g C.∘ h)
∼-congʳ h {f} {g} p = mk∼ (begin
  F₁ (f C.∘ h)     ≈⟨ homomorphism ⟩
  F₁ f D.∘ F₁ h    ≈⟨ D.∘-resp-≈ˡ (run∼ p) ⟩
  F₁ g D.∘ F₁ h    ≈⟨ homomorphism ⟨
  F₁ (g C.∘ h)     ∎)
  where open D.HomReasoning
