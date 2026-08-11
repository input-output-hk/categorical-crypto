{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; isEquivalence; trans)

open import Class.Decidable
open import Class.HasOrder
open import Algebra

import Data.List.NonEmpty as NE

open import Data.Rational as ℚ using (ℚ; _/_)
import Data.Rational.Properties as ℚP
open import Data.Integer using (+_)

open import ProbabilisticLogic.Abstract
open import ProbabilisticLogic.Reasoning

module ProbabilisticLogic.Examples.Coins c ℓ (a : Abstract c ℓ) where

-- `Prelude` deliberately stopped registering the product instance; the pair
-- sample space below needs it.
instance DecEq-×′ = DecEq-×

open Abstract a
open import ProbabilisticLogic.Logic c ℓ a

-- flipping 2 coins
Z = Bool × Bool

P : ProbDistr Z
P = empirical ((false , false) NE.∷ (false , true) ∷ (true , false) ∷ (true , true) ∷ [])

-- X: the first coin is `true`
-- Y: both coins are `true`
X Y : Z → Type
X ω = proj₁ ω ≡ true
Y ω = ω ≡ (true , true)

X↓ Y↓ : Z → Bool
X↓ ω = P.⌊ ¿ X ¿¹ ω ⌋
Y↓ ω = P.⌊ ¿ Y ¿¹ ω ⌋

-- X has probability at least 1/2
PX≥1/2 : Σ[ P ][ fromℚ (+ 1 / 2) ] X
PX≥1/2 .p≤PX = begin
  fromℚ (+ 1 / 2) ≈⟨ empirical-eq ⟨
  P ∙ (↑ X↓)      ≈⟨ P-Dec X ⟨
  P ∙ X ∎
  where open ≤-Reasoning Probability

-- If X is true, Y has probability at least 1/2
X⇒1/2Y : X ⇒[ P ][ fromℚ (+ 1 / 2) ] Y
X⇒1/2Y .p≤PX = begin
  fromℚ (+ 1 / 2)                                              ≈⟨ empirical-eq ⟨
  empirical ((true , false) NE.∷ (true , true) ∷ []) ∙ (↑ Y↓)  ≈⟨ cond-empirical P.refl ⟨
  (P ∣ (↑ X↓)) ∙ (↑ Y↓)                                        ≈⟨ ∣-cong (toWitness , fromWitness) ⟩
  (P ∣ X) ∙ (↑ Y↓)                                             ≈⟨ P-Dec Y ⟨
  (P ∣ X) ∙ Y ∎
  where open ≤-Reasoning Probability

-- This implies Y has probability at least 1/4
PY≥1/4 : Σ[ P ][ fromℚ (+ 1 / 4) ] Y
PY≥1/4 = Σ-resp-≈ fromℚ-homomorphism
  (app (fromℚ-nonneg (ℚP.nonNegative⁻¹ (+ 1 / 2)))
       (fromℚ-nonneg (ℚP.nonNegative⁻¹ (+ 1 / 2)))
       X⇒1/2Y PX≥1/2)
