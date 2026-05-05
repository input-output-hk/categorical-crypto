{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; _⊗_; isEquivalence; trans)

open import Class.HasOrder
open import Algebra
open import Algebra.Morphism.Structures using (module SemiringMorphisms)
open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Unary

import Data.List.NonEmpty as NE

open import Data.Rational as ℚ using (ℚ; _/_)
import Data.Rational.Properties as ℚP
open import Data.Integer using (+_)

open import ProbabilisticLogic.Reasoning

module ProbabilisticLogic.Abstract where

private variable Ω Ω₁ Ω₂ : Type

disjoint : (P Q : Ω → Type) → Type
disjoint P Q = ∀ {ω} → P ω → Q ω → ⊥

↑_ : (Ω → Bool) → Ω → Type
↑_ X = T P.∘ X

infixr 6 _⊠_
_⊠_ : (Ω₁ → Type) → (Ω₂ → Type) → Ω₁ × Ω₂ → Type
(X ⊠ Y) (a , b) = X a × Y b

record AbstractProbability c ℓ : Type (sucˡ (c ⊔ˡ ℓ)) where
  field Probabilityᴿ : CommutativeSemiring c ℓ

  open CommutativeSemiring Probabilityᴿ renaming (Carrier to Probability) public

  field _⁻¹ : (p : Probability) → ¬ p ≈ 0# → Probability
        d : Probability → Probability → Probability
        ⦃ HasPartialOrder-Probability ⦄
          : HasPartialOrder {A = Probability} {_≈_ = _≈_} {ℓ″ = ℓ} {ℓ‴ = ℓ}
        ≤-cong : ∀ {p p' q q' : Probability} → p ≤ p' → q ≤ q' → p * q ≤ p' * q'
        +-mono-≤ : ∀ {p p' q q' : Probability} → p ≤ p' → q ≤ q' → p + q ≤ p' + q'
        +-cancelʳ-≤ : ∀ {p q r : Probability} → p + r ≤ q + r → p ≤ q
        fromℚ : ℚ → Probability
        fromℚ-isSemiringHomomorphism
          : SemiringMorphisms.IsSemiringHomomorphism ℚP.+-*-rawSemiring rawSemiring fromℚ

  open SemiringMorphisms ℚP.+-*-rawSemiring rawSemiring
  open IsSemiringHomomorphism fromℚ-isSemiringHomomorphism public
    using (1#-homo)
    renaming (+-homo to fromℚ-+-homo; *-homo to fromℚ-*-homo; 0#-homo to fromℚ-0)

  fromℚ-homomorphism : ∀ {p q} → fromℚ p * fromℚ q ≈ fromℚ (p ℚ.* q)
  fromℚ-homomorphism {p} {q} = Eq.sym (fromℚ-*-homo p q)
    where module Eq = Setoid setoid

  fromℚ-1 : fromℚ (+ 1 / 1) ≈ 1#
  fromℚ-1 = 1#-homo

record Abstract c ℓ : Type (sucˡ (c ⊔ˡ ℓ)) where
  field abstractProbability : AbstractProbability c ℓ

  open AbstractProbability abstractProbability public

  field -- we assume discrete probability distributions, which don't need a σ-algebra
        ProbDistr : Type → Type c
        _∙_ : ProbDistr Ω → (Ω → Type) → Probability
        _∣_ : ProbDistr Ω → (X : Ω → Type) → ProbDistr Ω
        P∅≈0 : {P : ProbDistr Ω} → P ∙ ∅ ≈ 0#
        PU≈1 : {P : ProbDistr Ω} → P ∙ U ≈ 1#
        P-distrib-disjoint : ∀ {X Y} {P : ProbDistr Ω} → disjoint X Y → P ∙ X + P ∙ Y ≈ P ∙ (X ∪ Y)
        cond-probability : ∀ {P : ProbDistr Ω} {X Y} → P ∙ X * (P ∣ X) ∙ Y ≈ P ∙ (X ∩ Y)
        prob-monotonous : ∀ {P : ProbDistr Ω} {X Y} → X ⊆ Y → P ∙ X ≤ P ∙ Y
        ∣-cong : ∀ {P : ProbDistr Ω} {X X' Y : Ω → Type}
               → X ≐ X' → (P ∣ X) ∙ Y ≈ (P ∣ X') ∙ Y
        empirical : (l : NE.List⁺ Ω) → ProbDistr Ω
        empirical-eq : ∀ {l} {X : Ω → Bool}
                     → empirical l ∙ (↑ X) ≈ fromℚ (+ length (filterᵇ X (NE.toList l)) / NE.length l)
        cond-empirical : ∀ {l l'} {X : Ω → Bool} {Y : Ω → Type}
                       → filterᵇ X (NE.toList l) ≡ NE.toList l'
                       → (empirical l ∣ (↑ X)) ∙ Y ≈ empirical l' ∙ Y
        _⊗_ : ProbDistr Ω₁ → ProbDistr Ω₂ → ProbDistr (Ω₁ × Ω₂)
        ⊗-rect : ∀ {P : ProbDistr Ω₁} {Q : ProbDistr Ω₂} {X : Ω₁ → Type} {Y : Ω₂ → Type}
               → (P ⊗ Q) ∙ (X ⊠ Y) ≈ P ∙ X * Q ∙ Y

  private variable P : ProbDistr Ω
                   X Y : Ω → Type

  ∙-cong : X ≐ Y → P ∙ X ≈ P ∙ Y
  ∙-cong (X⊆Y , Y⊆X) = ≤-antisym (prob-monotonous X⊆Y) (prob-monotonous Y⊆X)

  0≤PX : 0# ≤ P ∙ X
  0≤PX {P = P} {X} = begin
    0#    ≈⟨ P∅≈0 ⟨
    P ∙ ∅ ≤⟨ prob-monotonous (λ ()) ⟩
    P ∙ X ∎
    where open ≤-Reasoning Probability

  PX≤1 : P ∙ X ≤ 1#
  PX≤1 {P = P} {X} = begin
    P ∙ X ≤⟨ prob-monotonous (λ _ → tt) ⟩
    P ∙ U ≈⟨ PU≈1 ⟩
    1#    ∎
    where open ≤-Reasoning Probability

  module _ {P : ProbDistr Ω₁} {Q : ProbDistr Ω₂} where
    open ≈-Reasoning setoid
    ⊗-marg₁ : ∀ {X : Ω₁ → Type} → (P ⊗ Q) ∙ (X P.∘ proj₁) ≈ P ∙ X
    ⊗-marg₁ {X} = begin
      (P ⊗ Q) ∙ (X P.∘ proj₁) ≈⟨ ∙-cong ((λ Xa → Xa , tt) , proj₁) ⟩
      (P ⊗ Q) ∙ (X ⊠ U)       ≈⟨ ⊗-rect ⟩
      P ∙ X * Q ∙ U           ≈⟨ *-congˡ PU≈1 ⟩
      P ∙ X * 1#              ≈⟨ *-identityʳ _ ⟩
      P ∙ X                   ∎

    ⊗-marg₂ : ∀ {Y : Ω₂ → Type} → (P ⊗ Q) ∙ (Y P.∘ proj₂) ≈ Q ∙ Y
    ⊗-marg₂ {Y} = begin
      (P ⊗ Q) ∙ (Y P.∘ proj₂) ≈⟨ ∙-cong ((λ Yb → tt , Yb) , proj₂) ⟩
      (P ⊗ Q) ∙ (U ⊠ Y)       ≈⟨ ⊗-rect ⟩
      P ∙ U * Q ∙ Y           ≈⟨ *-congʳ PU≈1 ⟩
      1# * Q ∙ Y              ≈⟨ *-identityˡ _ ⟩
      Q ∙ Y                   ∎

    ⊗-cond-* : ∀ {X : Ω₁ → Type} {Y : Ω₂ → Type}
             → P ∙ X * ((P ⊗ Q) ∣ (X P.∘ proj₁)) ∙ (Y P.∘ proj₂) ≈ P ∙ X * Q ∙ Y
    ⊗-cond-* {X} {Y} = begin
      P ∙ X * ((P ⊗ Q) ∣ (X P.∘ proj₁)) ∙ (Y P.∘ proj₂)
        ≈⟨ *-congʳ ⊗-marg₁ ⟨
      (P ⊗ Q) ∙ (X P.∘ proj₁) * ((P ⊗ Q) ∣ (X P.∘ proj₁)) ∙ (Y P.∘ proj₂)
        ≈⟨ cond-probability ⟩
      (P ⊗ Q) ∙ ((X P.∘ proj₁) ∩ (Y P.∘ proj₂))
        ≈⟨ ⊗-rect ⟩
      P ∙ X * Q ∙ Y ∎

  empirical-⊗-rect : ∀ {l₁ : NE.List⁺ Ω₁} {l₂ : NE.List⁺ Ω₂} {X : Ω₁ → Bool} {Y : Ω₂ → Bool}
    → (empirical l₁ ⊗ empirical l₂) ∙ ((↑ X) ⊠ (↑ Y))
    ≈ fromℚ (+ length (filterᵇ X (NE.toList l₁)) / NE.length l₁)
        * fromℚ (+ length (filterᵇ Y (NE.toList l₂)) / NE.length l₂)
  empirical-⊗-rect {l₁ = l₁} {l₂} {X} {Y} = begin
    (empirical l₁ ⊗ empirical l₂) ∙ ((↑ X) ⊠ (↑ Y))
      ≈⟨ ⊗-rect ⟩
    empirical l₁ ∙ (↑ X) * empirical l₂ ∙ (↑ Y)
      ≈⟨ *-cong empirical-eq empirical-eq ⟩
    fromℚ (+ length (filterᵇ X (NE.toList l₁)) / NE.length l₁)
      * fromℚ (+ length (filterᵇ Y (NE.toList l₂)) / NE.length l₂) ∎
    where open ≈-Reasoning setoid
