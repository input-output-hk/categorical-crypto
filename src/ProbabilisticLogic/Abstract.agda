{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; isEquivalence; trans)

open import Class.HasOrder
open import Algebra
open import Relation.Unary

import Data.List.NonEmpty as NE

open import Data.Rational as ℚ using (ℚ; _/_)
open import Data.Integer using (+_)

module ProbabilisticLogic.Abstract where

private variable Ω : Type

disjoint : (P Q : Ω → Type) → Type
disjoint P Q = ∀ {ω} → P ω → Q ω → ⊥

↑_ : (Ω → Bool) → Ω → Type
↑_ X = T P.∘ X

record AbstractProbability : Type₁ where
  field Probabilityᴿ : CommutativeRing 0ℓ 0ℓ

  open CommutativeRing Probabilityᴿ renaming (Carrier to Probability) public

  field _⁻¹ : (p : Probability) → {p ≢ 0#} → Probability
        d : Probability → Probability → Probability
        ⦃ HasPartialOrder-Probability ⦄ : HasPartialOrder {A = Probability} {_≈_ = _≈_}
        ≤-cong : ∀ {p p' q q' : Probability} → p ≤ p' → q ≤ q' → p * q ≤ p' * q'
        fromℚ : ℚ → Probability
        fromℚ-homomorphism : ∀ {p q} → fromℚ p * fromℚ q ≈ fromℚ (p ℚ.* q)

record Abstract : Type₁ where
  field abstractProbability : AbstractProbability

  open AbstractProbability abstractProbability public

  field -- we assume discrete probability distributions, which don't need a σ-algebra
        ProbDistr : Type → Type
        _∙_ : ProbDistr Ω → (Ω → Type) → Probability
        _∣_ : ProbDistr Ω → (X : Ω → Type) → ProbDistr (Σ Ω X)
        extend : ∀ {X} → ProbDistr (Σ Ω X) → ProbDistr Ω
        P∅≈0 : {P : ProbDistr Ω} → P ∙ ∅ ≈ 0#
        PU≤1 : {P : ProbDistr Ω} → P ∙ U ≤ 1#
        P-distrib-disjoint : ∀ {X Y} {P : ProbDistr Ω} → disjoint X Y → P ∙ X + P ∙ Y ≈ P ∙ (X ∪ Y)
        cond-probability : ∀ {P : ProbDistr Ω} {X Y} → P ∙ X * (extend (P ∣ X)) ∙ Y ≈ P ∙ (X ∩ Y)
        prob-monotonous : ∀ {P : ProbDistr Ω} {X Y} → X ⊆ Y → P ∙ X ≤ P ∙ Y
        extend-∣ : ∀ {P : ProbDistr Ω} {X Y} → extend (P ∣ X) ∙ Y ≈ (P ∣ X) ∙ (Y ∘ proj₁)
        extend-∣-cong : ∀ {P : ProbDistr Ω} {X X' Y : Ω → Type}
                      → X ≐ X' → extend (P ∣ X) ∙ Y ≈ extend (P ∣ X') ∙ Y
        uniformFromList : (l : NE.List⁺ Ω) → ProbDistr Ω
        uniform-eq : ∀ {l} {X : Ω → Bool}
                   → uniformFromList l ∙ (↑ X) ≈ fromℚ (+ length (filterᵇ X (NE.toList l)) / NE.length l)
        cond-uniform : ∀ {l l'} {X : Ω → Bool} {Y : Ω → Type}
                     → filterᵇ X (NE.toList l) ≡ NE.toList l'
                     → extend (uniformFromList l ∣ (↑ X)) ∙ Y ≈ uniformFromList l' ∙ Y

  ∙-cong : {P : ProbDistr Ω} {X Y : Ω → Type} → X ≐ Y → P ∙ X ≈ P ∙ Y
  ∙-cong (X⊆Y , Y⊆X) = ≤-antisym (prob-monotonous X⊆Y) (prob-monotonous Y⊆X)
