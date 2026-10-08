{-# OPTIONS --safe --without-K #-}

-- stdlib 2.3 stops at dependent dsubst₂ and lacks these subst₂ groupoid laws.

module Relation.Binary.PropositionalEquality.Properties.Ext where

open import Relation.Binary.PropositionalEquality.Core

subst₂-sym-flip : ∀ {A B : Set} {P : A → B → Set} {a a'} {b b'}
                → (p : a ≡ a') (q : b ≡ b') {x : P a b} {y : P a' b'}
                → subst₂ P p q x ≡ y → subst₂ P (sym p) (sym q) y ≡ x
subst₂-sym-flip refl refl refl = refl

subst₂-trans : ∀ {A B : Set} {P : A → B → Set} {a₁ a₂ a₃} {b₁ b₂ b₃}
             → (p : a₁ ≡ a₂) (p' : a₂ ≡ a₃) (q : b₁ ≡ b₂) (q' : b₂ ≡ b₃)
             → (x : P a₁ b₁)
             → subst₂ P p' q' (subst₂ P p q x)
             ≡ subst₂ P (trans p p') (trans q q') x
subst₂-trans refl refl refl refl _ = refl
