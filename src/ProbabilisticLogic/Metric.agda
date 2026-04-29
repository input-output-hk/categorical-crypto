{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude hiding (pure; _>>=_; _⊎_; _*_; _/_; isEquivalence; trans)

open import Class.HasOrder

open import ProbabilisticLogic.Abstract

module ProbabilisticLogic.Metric (a : Abstract) where

open Abstract a

private variable Ω : Type

record isSupremum {a} (T : Type a) (f : T → Probability) (p : Probability) : Type a where
  field isUpperBound : ∀ {t} → f t ≤ p
        isLeastUpperBound : ∀ {q} → q < p → ∃[ t ] ¬ f t ≤ q

dTV_,_≡_ : (P Q : ProbDistr Ω) → (p : Probability) → Type₁
dTV_,_≡_ {Ω} P Q p = isSupremum (Ω → Type) (λ X → d (P ∙ X) (Q ∙ X)) p
