{-# OPTIONS --safe --without-K --guardedness #-}

module ProbabilisticLogic.Dp.Positive.Monad where

open import Data.Nat.Base using (_+_; suc)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties
open import Level using (Level)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Paths

private variable
  a b : Level
  A : Set a
  B : Set b

infix 4 _≼₊_ _≈₊_

_≼₊_ : Dₚ A → Dₚ A → Set _
d ≼₊ e = ∀ P → NNF P → PositiveTest d P → PositiveTest e P

_≈₊_ : Dₚ A → Dₚ A → Set _
d ≈₊ e = (d ≼₊ e) × (e ≼₊ d)

≈ₚ⇒≈₊ : {d e : Dₚ A} → d ≈ₚ e → d ≈₊ e
≈ₚ⇒≈₊ eq = (λ P nn → positive-test-to nn (proj₁ eq)) , λ P nn → positive-test-to nn (proj₂ eq)

≈₊-refl : {d : Dₚ A} → d ≈₊ d
≈₊-refl = (λ P nn p → p) , λ P nn p → p

≈₊-sym : {d e : Dₚ A} → d ≈₊ e → e ≈₊ d
≈₊-sym = swap

≈₊-trans : {d e f : Dₚ A} → d ≈₊ e → e ≈₊ f → d ≈₊ f
≈₊-trans de ef = (λ P nn p → proj₁ ef P nn (proj₁ de P nn p)) ,
  λ P nn p → proj₂ de P nn (proj₂ ef P nn p)

≈₊-isEquivalence : IsEquivalence (_≈₊_ {A = A})
≈₊-isEquivalence = record { refl = ≈₊-refl ; sym = ≈₊-sym ; trans = ≈₊-trans }

bind-witness : (d : Dₚ A) (f : A → Dₚ B) (P : B → ℚ) → NNF P
             → {x : A} → Positive d x → PositiveTest (f x) P → PositiveTest (d >>=ₚ f) P
bind-witness d f P nn path (m , pos) =
  let n , outer = positive-witness (λ x → cum m (f x) P) (λ x → cum-nn m (f x) P nn) path pos
  in n + m , <-≤-trans outer (>>=ₚ-boundB n m d f P nn)

bind-positive-to : (d e : Dₚ A) (f g : A → Dₚ B) → d ≼₊ e → (∀ x → f x ≼₊ g x)
                 → (d >>=ₚ f) ≼₊ (e >>=ₚ g)
bind-positive-to d e f g de fg P nn (n , pos) =
  let test = λ x → cum n (f x) P
      test-nn = λ x → cum-nn n (f x) P nn
      m , outer = de test test-nn (n , <-≤-trans pos (>>=ₚ-boundA n d f P nn))
      x , path , inner = positive-extract m e test test-nn outer
  in bind-witness e g P nn path (fg x P nn (n , inner))

bind-cong : (d e : Dₚ A) (f g : A → Dₚ B) → d ≈₊ e → (∀ x → f x ≈₊ g x)
          → (d >>=ₚ f) ≈₊ (e >>=ₚ g)
bind-cong d e f g de fg =
  bind-positive-to d e f g (proj₁ de) (λ x → proj₁ (fg x)) ,
  bind-positive-to e d g f (proj₂ de) (λ x → proj₂ (fg x))

map-cong : (f : A → B) {d e : Dₚ A} → d ≈₊ e → mapₚ f d ≈₊ mapₚ f e
map-cong f {d} {e} de = bind-cong d e (λ x → returnₚ (f x)) (λ x → returnₚ (f x)) de (λ x → ≈₊-refl)

map-positive-to : (f : A → B) (d : Dₚ A) (P : B → ℚ) → NNF P
                → PositiveTest d (λ x → P (f x)) → PositiveTest (mapₚ f d) P
map-positive-to f d P nn (n , pos) =
  suc n , subst (0ℚ ℚ.<_) (sym (mapₚ-cum n f d P)) pos

map-positive-from : (f : A → B) (d : Dₚ A) (P : B → ℚ) → NNF P
                  → PositiveTest (mapₚ f d) P → PositiveTest d (λ x → P (f x))
map-positive-from f d P nn (n , pos) = n , <-≤-trans pos (mapₚ-≤ n f d P nn)
