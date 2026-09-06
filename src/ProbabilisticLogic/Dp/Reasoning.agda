{-# OPTIONS --safe --without-K --guardedness #-}

-- Implicit-subject forms of `Dₚ`'s setoid and bind laws.
--
-- `Dp`'s own lemmas take their subjects explicitly, which is what keeps that
-- hierarchy elaborating in seconds but leaves every `≈ₚ` chain naming the terms
-- it is about; passed implicitly they get stranded as metas.  These wrappers pin
-- the subjects from the goal instead, so a chain reads as a chain.

open import Level using (Level)

open import ProbabilisticLogic.Dp

module ProbabilisticLogic.Dp.Reasoning where

private variable
  a : Level
  A B : Set a

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
