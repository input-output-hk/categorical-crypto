{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; isEquivalence; trans)

open import Class.Decidable
open import Class.HasOrder
open import Algebra
open import Relation.Unary
open import Relation.Binary using (Setoid)

open import ProbabilisticLogic.Abstract
open import ProbabilisticLogic.Reasoning

module ProbabilisticLogic.Logic (a : Abstract) where

open Abstract a

private module Eq = Setoid setoid

private variable Ω : Type

record Σ[_][_]_ (P : ProbDistr Ω) (p : Probability) (X : Ω → Type) : Type₁ where
  field p≤PX : p ≤ P ∙ X

open Σ[_][_]_ public

Σ-resp-≈ : {P : ProbDistr Ω} {X : Ω → Type} {p p' : Probability}
         → p ≈ p' → Σ[ P ][ p ] X → Σ[ P ][ p' ] X
Σ-resp-≈ {P = P} {X} {p} {p'} p≈p' σ .p≤PX = begin
  p'    ≈⟨ p≈p' ⟨
  p     ≤⟨ σ .p≤PX ⟩
  P ∙ X ∎
  where open ≤-Reasoning Probability

_⇒[_][_]_ : (X : Ω → Type) (P : ProbDistr Ω) (p : Probability) (Y : Ω → Type) → Type₁
X ⇒[ P ][ p ] Y = Σ[ P ∣ X ][ p ] (Y ∘ proj₁)

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
