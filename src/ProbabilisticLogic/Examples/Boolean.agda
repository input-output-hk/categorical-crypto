{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; isEquivalence; trans)

open import Class.Decidable
open import Class.HasOrder
open import Algebra

import Data.List.NonEmpty as NE

open import Data.Rational as ℚ using (ℚ; _/_)
open import Data.Integer using (+_)

open import ProbabilisticLogic.Abstract
open import ProbabilisticLogic.Reasoning

module ProbabilisticLogic.Examples.Boolean c ℓ (a : Abstract c ℓ) where

open Abstract a
open import ProbabilisticLogic.Logic c ℓ a

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
  fromℚ (+ 1 / 2) ≈⟨ uniform-eq ⟨
  P ∙ (↑ X↓)      ≈⟨ P-Dec X ⟨
  P ∙ X ∎
  where open ≤-Reasoning Probability

X⇒1/2Y : X ⇒[ P ][ fromℚ (+ 1 / 2) ] Y
X⇒1/2Y .p≤PX = begin
  fromℚ (+ 1 / 2)                                                  ≈⟨ uniform-eq ⟨
  uniformFromList ((true , false) NE.∷ (true , true) ∷ []) ∙ (↑ Y↓) ≈⟨ cond-uniform P.refl ⟨
  (P ∣ (↑ X↓)) ∙ (↑ Y↓)                                            ≈⟨ ∣-cong (toWitness , fromWitness) ⟩
  (P ∣ X) ∙ (↑ Y↓)                                                 ≈⟨ P-Dec Y ⟨
  (P ∣ X) ∙ Y ∎
  where open ≤-Reasoning Probability

PY≥1/4 : Σ[ P ][ fromℚ (+ 1 / 4) ] Y
PY≥1/4 = Σ-resp-≈ fromℚ-homomorphism (app X⇒1/2Y PX≥1/2)
