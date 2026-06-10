open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; isEquivalence; trans)

open import Class.Decidable
open import Class.HasOrder
open import Algebra
open import Relation.Unary
open import Relation.Binary

import Data.List.NonEmpty as NE

open import Data.Rational as ℚ using (ℚ; _/_)
open import Data.Integer using (+_)

module ProbabilisticLogic where

import Relation.Binary.Reasoning.PartialOrder as ≤-Reasoning'

module ≤-Reasoning {a} (A : Type a) ⦃ po : HasPartialOrder {a} {A} {_≈_ = _≡_} {lzero} {lzero} ⦄ where
  open ≤-Reasoning' record { isPartialOrder = ≤-isPartialOrder {A = A} } public

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
        ⦃ HasPartialOrder-Probability ⦄ : HasPartialOrder≡ {A = Probability}
        ≤-cong : ∀ {p p' q q' : Probability} → p ≤ p' → q ≤ q' → p * q ≤ p' * q'
        fromℚ : ℚ → Probability
        fromℚ-homomorphism : ∀ {p q} → fromℚ p * fromℚ q ≡ fromℚ (p ℚ.* q)

record Abstract : Type₁ where
  field abstractProbability : AbstractProbability

  open AbstractProbability abstractProbability public

  field -- we assume discrete probability distributions, which don't need a σ-algebra
        ProbDistr : Type → Type
        _∙_ : ProbDistr Ω → (Ω → Type) → Probability
        _∣_ : ProbDistr Ω → (X : Ω → Type) → ProbDistr (Σ Ω X)
        extend : ∀ {X} → ProbDistr (Σ Ω X) → ProbDistr Ω
        P∅≡0 : {P : ProbDistr Ω} → P ∙ ∅ ≡ 0#
        PU≤1 : {P : ProbDistr Ω} → P ∙ U ≤ 1#
        P-distrib-disjoint : ∀ {X Y} {P : ProbDistr Ω} → disjoint X Y → P ∙ X + P ∙ Y ≡ P ∙ (X ∪ Y)
        cond-probability : ∀ {P : ProbDistr Ω} {X Y} → P ∙ X * (extend (P ∣ X)) ∙ Y ≡ P ∙ (X ∩ Y)
        prob-monotonous : ∀ {P : ProbDistr Ω} {X Y} → X ⊆ Y → P ∙ X ≤ P ∙ Y
        extend-∣ : ∀ {P : ProbDistr Ω} {X Y} → extend (P ∣ X) ∙ Y ≡ (P ∣ X) ∙ (Y ∘ proj₁)
        uniformFromList : (l : NE.List⁺ Ω) → ProbDistr Ω
        uniform-eq : ∀ {l} {X : Ω → Bool}
                   → uniformFromList l ∙ (↑ X) ≡ fromℚ (+ length (filterᵇ X (NE.toList l)) / NE.length l)

  ∙-cong : {P : ProbDistr Ω} {X Y : Ω → Type} → X ≐ Y → P ∙ X ≡ P ∙ Y
  ∙-cong (X⊆Y , Y⊆X) = ≤-antisym (prob-monotonous X⊆Y) (prob-monotonous Y⊆X)

  cond-uniform : ∀ {l l'} {X Y : Ω → Bool}
               → filterᵇ X (NE.toList l) ≡ NE.toList l'
               → extend (uniformFromList l ∣ (↑ X)) ∙ (↑ Y) ≡ uniformFromList l' ∙ (↑ Y)
  cond-uniform = {!!}

module Logic (a : Abstract) where
  open Abstract a

  record isSupremum {a} (T : Type a) (f : T → Probability) (p : Probability) : Type a where
    field isUpperBound : ∀ {t} → f t ≤ p
          isLeastUpperBound : ∀ {q} → q < p → ∃[ t ] ¬ f t ≤ q

  dTV_,_≡_ : (P Q : ProbDistr Ω) → (p : Probability) → Type₁
  dTV_,_≡_ {Ω} P Q p = isSupremum (Ω → Type) (λ X → d (P ∙ X) (Q ∙ X)) p

  -- record ConcreteProbability (P : ProbDistr Ω) : Type₁ where
  --   field X : Ω → Type
  --         p : Probability
  --         PX≡p : P ∙ X ≡ p

  -- _+ₚ_ : {P : ProbDistr Ω} → ConcreteProbability P → ConcreteProbability P → ConcreteProbability P
  -- p +ₚ q = let module p = ConcreteProbability p; module q = ConcreteProbability q in
  --   record { X = p.X ∪ q.X ; p = {!!} ; PX≡p = {!!} }

  record Σ[_][_]_ (P : ProbDistr Ω) (p : Probability) (X : Ω → Type) : Type₁ where
    field p≤PX : p ≤ P ∙ X

  open Σ[_][_]_

  _⇒[_][_]_ : (X : Ω → Type) (P : ProbDistr Ω) (p : Probability) (Y : Ω → Type) → Type₁
  X ⇒[ P ][ p ] Y = Σ[ P ∣ X ][ p ] (Y ∘ proj₁)

  app : {P : ProbDistr Ω} {p q : Probability} {X Y : Ω → Type}
      → X ⇒[ P ][ q ] Y → Σ[ P ][ p ] X → Σ[ P ][ p * q ] Y
  app {P = P} {p} {q} {X} {Y} record { p≤PX = p₁ } record { p≤PX = p₂ } .p≤PX = begin
    p * q                         ≤⟨ ≤-cong p₂ p₁ ⟩
    P ∙ X * (P ∣ X) ∙ (Y ∘ proj₁) ≡⟨ cong (P ∙ X *_) extend-∣ ⟨
    P ∙ X * (extend (P ∣ X)) ∙ Y  ≡⟨ cond-probability ⟩
    P ∙ (X ∩ Y)                   ≤⟨ prob-monotonous proj₂ ⟩
    P ∙ Y ∎
    where open ≤-Reasoning Probability

  P-Dec : {P : ProbDistr Ω} (X : Ω → Type) ⦃ X? : X ⁇¹ ⦄ → P ∙ X ≡ P ∙ (λ ω → True (¿ X ω ¿))
  P-Dec X = ∙-cong {!!}

  module Example where
    Z = Bool × Bool

    P : ProbDistr Z
    P = uniformFromList ((false , false) NE.∷ (false , true) ∷ (true , false) ∷ (true , true) ∷ [])

    X Y : Z → Type
    X ω = proj₁ ω ≡ true
    Y ω = ω ≡ (true , true)

    X↓ Y↓ : Z → Bool
    X↓ ω = P.⌊ ¿ X ¿¹ ω ⌋
    Y↓ ω = P.⌊ ¿ Y ¿¹ ω ⌋

    PX≥1/2 : Σ[ P ][ fromℚ (+ 1 / 2) ] X
    PX≥1/2 .p≤PX = begin
      fromℚ (+ 1 / 2) ≈⟨ P.sym uniform-eq ⟩
      P ∙ (↑ X↓)      ≈⟨ P.sym (P-Dec X) ⟩
      P ∙ X ∎
      where open ≤-Reasoning Probability

    X⇒1/2Y : X ⇒[ P ][ fromℚ (+ 1 / 2) ] Y
    X⇒1/2Y .p≤PX = begin
      fromℚ (+ 1 / 2) ≈⟨ P.sym uniform-eq ⟩
      uniformFromList ((true , false) NE.∷ (true , true) ∷ []) ∙ (↑ Y↓) ≈⟨ P.sym (cond-uniform P.refl) ⟩
      extend (P ∣ (↑ X↓)) ∙ (↑ Y↓) ≈⟨ cong (_∙ (↑ Y↓)) {!!} ⟩
      extend (P ∣ X) ∙ (↑ Y↓) ≈⟨ P.sym (P-Dec Y) ⟩
      extend (P ∣ X) ∙ Y ≈⟨ extend-∣ ⟩
      (P ∣ X) ∙ (Y ∘ proj₁) ∎
      where open ≤-Reasoning Probability

    PY≥1/4 : Σ[ P ][ fromℚ (+ 1 / 4) ] Y
    PY≥1/4 = subst (λ x → Σ[ P ][ x ] Y) fromℚ-homomorphism (app X⇒1/2Y PX≥1/2)


--------------------------------------------------------------------------------
-- Idea

-- Measure Ω = (Ω → Type) → ℚ → Type
-- μ ∙ X ≡ m = μ X m

-- record Meas : Type₁ where
--   field Ω : Type
--         μ : Measure Ω
--         X : Ω → Type

-- _≈ₚ_ : Meas → Meas → Type
-- (Ω₁ , P₁ , X₁) ≈ₚ (Ω₂ , P₂ , X₂) = ∃[ p ] P₁ ∙ X₁ ≡ p × P₂ ∙ X₂ ≡ p

-- fromℚ : ℚ → Meas
-- fromℚ (m / n) = (Fin n , uniform , _≤ m)

-- _∙_ : Measure Ω → (Ω → Type) → Meas
-- P ∙ X = (_ , P , X)

-- pushforward : (Ω₁ → Ω₂) → Meas Ω₁ → Meas Ω₂
-- pushforward f μ X m = μ ∙ (λ ω₂ → ∃[ ω₁ ] f ω₁ ≡ ω₂ × X ω₁) ≡ m

-- _+ₘ_ _*ₘ_ : Meas Ω → Meas Ω → Meas Ω

-- _+ₘ'_ : Meas Ω₁ → Meas Ω₂ → Meas (Ω₁ ⊎ Ω₂)
-- μ₁ +ₘ' μ₂ = pushforward inj₁ μ₁ +ₘ pushforward inj₂ μ₂

-- _+_ : Meas → Meas → Meas
-- (Ω₁ , μ₁ , X₁) + (Ω₂ , μ₂ , X₂) = (Ω₁ ⊎ Ω₂ , μ₁ +ₘ' μ₂ , [ X₁ , X₂ ])
