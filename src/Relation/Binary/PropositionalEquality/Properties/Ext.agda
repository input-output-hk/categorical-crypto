{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Extensions to `Relation.Binary.PropositionalEquality.Properties`: the
-- `subst₂` groupoid laws.  stdlib 2.3 has none of them (it stops at the
-- dependent `dsubst₂`).
------------------------------------------------------------------------

module Relation.Binary.PropositionalEquality.Properties.Ext where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst₂)

-- Inverse, read as an equation flip: `subst₂ P (sym p) (sym q)` undoes
-- `subst₂ P p q`, so a forwards transport equation runs backwards.  At
-- `refl` it is plain two-sided cancellation.
subst₂-sym-flip : ∀ {A B : Set} {P : A → B → Set} {a a'} {b b'}
                → (p : a ≡ a') (q : b ≡ b') {x : P a b} {y : P a' b'}
                → subst₂ P p q x ≡ y → subst₂ P (sym p) (sym q) y ≡ x
subst₂-sym-flip refl refl refl = refl

-- Composition: two nested transports collapse.
subst₂-trans : ∀ {A B : Set} {P : A → B → Set} {a₁ a₂ a₃} {b₁ b₂ b₃}
             → (p : a₁ ≡ a₂) (p' : a₂ ≡ a₃) (q : b₁ ≡ b₂) (q' : b₂ ≡ b₃)
             → (x : P a₁ b₁)
             → subst₂ P p' q' (subst₂ P p q x)
             ≡ subst₂ P (trans p p') (trans q q') x
subst₂-trans refl refl refl refl _ = refl
