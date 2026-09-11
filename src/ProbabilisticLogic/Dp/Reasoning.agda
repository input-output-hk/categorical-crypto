{-# OPTIONS --safe --without-K --guardedness #-}

-- Implicit-subject forms of `Dₚ`'s setoid and bind laws.
--
-- `Dp`'s own lemmas take their subjects explicitly, which is what keeps that
-- hierarchy elaborating in seconds but leaves every `≈ₚ` chain naming the terms
-- it is about; passed implicitly they get stranded as metas.  These wrappers pin
-- the subjects from the goal instead, so a chain reads as a chain.

open import Function.Base using (_∘′_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ProbabilisticLogic.Dp

module ProbabilisticLogic.Dp.Reasoning where

private variable
  a : Level
  A B C : Set a

infixr 5 _⟨≈⟩_

_⟨≈⟩_ : {d e h : Dₚ A} → d ≈ₚ e → e ≈ₚ h → d ≈ₚ h
_⟨≈⟩_ {d = d} {e} {h} = ≈ₚ-trans d e h

≈refl : {d : Dₚ A} → d ≈ₚ d
≈refl {d = d} = ≈ₚ-refl d

≈sym : {d e : Dₚ A} → d ≈ₚ e → e ≈ₚ d
≈sym {d = d} {e} = ≈ₚ-sym d e

-- Congruence in the continuation.
bindᶠ : {d : Dₚ A} {k l : A → Dₚ B} → ((x : A) → k x ≈ₚ l x) → (d >>=ₚ k) ≈ₚ (d >>=ₚ l)
bindᶠ {d = d} {k} {l} h = >>=ₚ-cong d d k l ≈refl h

-- Congruence in the subject.
bindˣ : {d e : Dₚ A} {k : A → Dₚ B} → d ≈ₚ e → (d >>=ₚ k) ≈ₚ (e >>=ₚ k)
bindˣ {d = d} {e} {k} h = >>=ₚ-cong d e k k h λ _ → ≈refl

-- `>>=ₚ-identityˡ` read backwards: introduce a junction.
push : (k : A → Dₚ B) (x : A) → k x ≈ₚ (returnₚ x >>=ₚ k)
push k x = ≈sym (>>=ₚ-identityˡ x k)

map-map : (d : Dₚ A) (h : A → B) (k : B → C) → mapₚ k (mapₚ h d) ≈ₚ mapₚ (k ∘′ h) d
map-map d h k = >>=ₚ-assoc d (returnₚ ∘′ h) (returnₚ ∘′ k)
          ⟨≈⟩ bindᶠ (λ x → >>=ₚ-identityˡ (h x) (returnₚ ∘′ k))

map-arg : {d e : Dₚ A} (h : A → B) → d ≈ₚ e → mapₚ h d ≈ₚ mapₚ h e
map-arg h de = bindˣ de

ret≡ : {x y : A} → x ≡ y → returnₚ x ≈ₚ returnₚ y
ret≡ refl = ≈refl

map-eq : (d : Dₚ A) (k l : A → B) → ((x : A) → k x ≡ l x) → mapₚ k d ≈ₚ mapₚ l d
map-eq d k l eq = bindᶠ λ x → ret≡ (eq x)

map-fuse : (d : Dₚ A) (h : A → B) (k : B → C) (l : A → C)
         → ((x : A) → k (h x) ≡ l x) → mapₚ k (mapₚ h d) ≈ₚ mapₚ l d
map-fuse d h k l eq = map-map d h k ⟨≈⟩ map-eq d (k ∘′ h) l eq

bind-map : (d : Dₚ A) (h : A → B) (k : B → Dₚ C) → (mapₚ h d >>=ₚ k) ≈ₚ (d >>=ₚ (k ∘′ h))
bind-map d h k = >>=ₚ-assoc d (returnₚ ∘′ h) k ⟨≈⟩ bindᶠ (λ x → >>=ₚ-identityˡ (h x) k)

map-bind : (d : Dₚ A) (h : A → Dₚ B) (k : B → C)
         → mapₚ k (d >>=ₚ h) ≈ₚ (d >>=ₚ λ x → mapₚ k (h x))
map-bind d h k = >>=ₚ-assoc d h (returnₚ ∘′ k)
