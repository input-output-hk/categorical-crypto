{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude hiding (pure; _>>=_; _⊎_; _*_; _/_; isEquivalence; trans)

open import Class.HasOrder

open import ProbabilisticLogic.Abstract

module ProbabilisticLogic.Metric ℓ (a : Abstract ℓ) where

open Abstract a

private variable Ω : Type

record isSupremum {a} (T : Set a) (f : T → Probability) (p : Probability) : Type (a ⊔ˡ ℓ) where
  field isUpperBound : ∀ {t} → f t ≤ p
        isLeastUpperBound : ∀ {q} → q < p → ∃[ t ] ¬ f t ≤ q

dTV_,_≡_ : (P Q : ProbDistr Ω) → (p : Probability) → Type (sucˡ lzero ⊔ˡ ℓ)
dTV_,_≡_ {Ω} P Q p = isSupremum (Ω → Type) (λ X → d (P ∙ X) (Q ∙ X)) p
