{-# OPTIONS --safe --without-K --guardedness #-}

module ProbabilisticLogic.Dp.Positive.Composition where

open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Sum.Properties using (inj₂-injective)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive

private variable
  a b : Level
  A : Set a
  B : Set b

bind-path : {d : Dₚ A} {f : A → Dₚ B} {x : A} {y : B}
           → Positive d x → Positive (f x) y → Positive (d >>=ₚ f) y
bind-path {f = f} (hit c pw eq) inner = delay c _ pw (cong (λ r → tagₚ r f) eq) inner
bind-path {f = f} (delay c e pw eq path) inner =
  delay c _ pw (cong (λ r → tagₚ r f) eq) (bind-path path inner)

no-tag-hit : (r : A ⊎ Dₚ A) (f : A → Dₚ B) {y : B} → tagₚ r f ≡ inj₁ y → ⊥
no-tag-hit (inj₁ x) f ()
no-tag-hit (inj₂ e) f ()

bind-unpath : {d : Dₚ A} {f : A → Dₚ B} {y : B}
             → Positive (d >>=ₚ f) y → ∃ λ x → Positive d x × Positive (f x) y
bind-unpath {d = d} {f} (hit c pw eq) = ⊥-elim (no-tag-hit (br d c) f eq)
bind-unpath {d = d} {f} {y} (delay c e pw eq path) with br d c in branch
... | inj₁ x = x , hit c pw branch , subst (λ e → Positive e y) (sym (inj₂-injective eq)) path
... | inj₂ d′ with inj₂-injective eq
... | refl =
  let x , outer , inner = bind-unpath path
  in x , delay c d′ pw branch outer , inner

map-path : (f : A → B) {d : Dₚ A} {x : A} → Positive d x → Positive (mapₚ f d) (f x)
map-path f {x = x} path = bind-path path (positive-return (f x))

map-unpath : (f : A → B) {d : Dₚ A} {y : B} → Positive (mapₚ f d) y
            → ∃ λ x → Positive d x × (f x ≡ y)
map-unpath f path =
  let x , outer , inner = bind-unpath path
  in x , outer , positive-return-reflect inner
