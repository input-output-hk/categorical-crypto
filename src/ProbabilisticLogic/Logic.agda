{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; isEquivalence; trans)

open import Class.Decidable
open import Class.HasOrder
open import Algebra
open import Relation.Unary
open import Relation.Binary using (Setoid)

open import ProbabilisticLogic.Abstract
open import ProbabilisticLogic.Reasoning

module ProbabilisticLogic.Logic ℓ (a : Abstract ℓ) where

open Abstract a

private module Eq = Setoid setoid

private variable Ω : Type

record Σ[_][_]_ (P : ProbDistr Ω) (p : Probability) (X : Ω → Type) : Type (sucˡ lzero ⊔ˡ ℓ) where
  field p≤PX : p ≤ P ∙ X

open Σ[_][_]_ public

Σ-resp-≈ : {P : ProbDistr Ω} {X : Ω → Type} {p p' : Probability}
         → p ≈ p' → Σ[ P ][ p ] X → Σ[ P ][ p' ] X
Σ-resp-≈ {P = P} {X} {p} {p'} p≈p' σ .p≤PX = begin
  p'    ≈⟨ p≈p' ⟨
  p     ≤⟨ σ .p≤PX ⟩
  P ∙ X ∎
  where open ≤-Reasoning Probability

Σ-resp-≐ : {P : ProbDistr Ω} {p : Probability} {X X' : Ω → Type}
         → X ≐ X' → Σ[ P ][ p ] X → Σ[ P ][ p ] X'
Σ-resp-≐ {P = P} {p} {X} {X'} X≐X' σ .p≤PX = begin
  p      ≤⟨ σ .p≤PX ⟩
  P ∙ X  ≈⟨ ∙-cong X≐X' ⟩
  P ∙ X' ∎
  where open ≤-Reasoning Probability

Σ-zero : {P : ProbDistr Ω} {X : Ω → Type} → Σ[ P ][ 0# ] X
Σ-zero .p≤PX = 0≤PX

Σ-weaken : {P : ProbDistr Ω} {X : Ω → Type} {p q : Probability}
         → p ≤ q → Σ[ P ][ q ] X → Σ[ P ][ p ] X
Σ-weaken {P = P} {X} {p} {q} p≤q σ .p≤PX = begin
  p     ≤⟨ p≤q ⟩
  q     ≤⟨ σ .p≤PX ⟩
  P ∙ X ∎
  where open ≤-Reasoning Probability

Σ-mono : {P : ProbDistr Ω} {p : Probability} {X Y : Ω → Type}
       → X ⊆ Y → Σ[ P ][ p ] X → Σ[ P ][ p ] Y
Σ-mono {P = P} {p} {X} {Y} X⊆Y σ .p≤PX = begin
  p     ≤⟨ σ .p≤PX ⟩
  P ∙ X ≤⟨ prob-monotonous X⊆Y ⟩
  P ∙ Y ∎
  where open ≤-Reasoning Probability

_⇒[_][_]_ : (X : Ω → Type) (P : ProbDistr Ω) (p : Probability) (Y : Ω → Type) → Set (sucˡ lzero ⊔ˡ ℓ)
X ⇒[ P ][ p ] Y = Σ[ P ∣ X ][ p ] (Y ∘ proj₁)

⇒-resp-≐-Y : {P : ProbDistr Ω} {p : Probability} {X Y Y' : Ω → Type}
           → Y ≐ Y' → X ⇒[ P ][ p ] Y → X ⇒[ P ][ p ] Y'
⇒-resp-≐-Y (Y⊆Y' , Y'⊆Y) = Σ-resp-≐ ((λ {ω} → Y⊆Y') , λ {ω} → Y'⊆Y)

app : {P : ProbDistr Ω} {p q : Probability} {X Y : Ω → Type}
    → X ⇒[ P ][ q ] Y → Σ[ P ][ p ] X → Σ[ P ][ p * q ] Y
app {P = P} {p} {q} {X} {Y} record { p≤PX = p₁ } record { p≤PX = p₂ } .p≤PX = begin
  p * q                         ≤⟨ ≤-cong p₂ p₁ ⟩
  P ∙ X * (P ∣ X) ∙ (Y ∘ proj₁) ≈⟨ *-cong Eq.refl extend-∣ ⟨
  P ∙ X * (extend (P ∣ X)) ∙ Y  ≈⟨ cond-probability ⟩
  P ∙ (X ∩ Y)                   ≤⟨ prob-monotonous proj₂ ⟩
  P ∙ Y ∎
  where open ≤-Reasoning Probability

P-Dec : {P : ProbDistr Ω} (X : Ω → Type) ⦃ X? : X ⁇¹ ⦄ → P ∙ X ≈ P ∙ (λ ω → True (¿ X ω ¿))
P-Dec X = ∙-cong (fromWitness , toWitness)
