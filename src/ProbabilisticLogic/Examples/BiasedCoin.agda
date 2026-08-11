{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; _⊗_; isEquivalence; trans)

open import Algebra

open import Data.Rational as ℚ using (ℚ; _/_)
open import Data.Integer using (+_)

open import ProbabilisticLogic.Abstract
open import ProbabilisticLogic.Reasoning

open import LibExt using (_⊠_)

module ProbabilisticLogic.Examples.BiasedCoin c ℓ (a : Abstract c ℓ) where

open Abstract a
open import ProbabilisticLogic.Logic c ℓ a
open import ProbabilisticLogic.Distribution.Bernoulli c ℓ a

-- A biased coin: lands `true` with probability 2/3.
biased : ProbDistr Bool
biased = bernoulli 2 1

-- Two independent biased coins, built directly via the product distribution
-- rather than spelling out all 9 weighted outcomes.
P : ProbDistr (Bool × Bool)
P = biased ⊗ biased

-- X: the first coin is `true`
-- Y: both coins are `true`
X Y : Bool × Bool → Type
X = (↑ id) P.∘ proj₁
Y = (↑ id) ⊠ (↑ id)

------------------------------------------------------------------------
-- Single-coin: the biased coin lands `true` with probability ≥ 2/3.

biased-single : Σ[ biased ][ fromℚ (+ 2 / 3) ] (↑ id)
biased-single .p≤PX = begin
  fromℚ (+ 2 / 3) ≈⟨ P-bernoulli-true 2 1 ⟨
  biased ∙ (↑ id) ∎
  where open ≤-Reasoning Probability

------------------------------------------------------------------------
-- Joint: marginalisation gives the first-coordinate event.

PX≥2/3 : Σ[ P ][ fromℚ (+ 2 / 3) ] X
PX≥2/3 .p≤PX = begin
  fromℚ (+ 2 / 3) ≈⟨ P-bernoulli-true 2 1 ⟨
  biased ∙ (↑ id) ≈⟨ ⊗-marg₁ ⟨
  P ∙ X           ∎
  where open ≤-Reasoning Probability

------------------------------------------------------------------------
-- Joint: the universal property gives the rectangle event directly.

PY≥4/9 : Σ[ P ][ fromℚ (+ 4 / 9) ] Y
PY≥4/9 .p≤PX = begin
  fromℚ (+ 4 / 9)
    ≈⟨ fromℚ-homomorphism ⟨
  fromℚ (+ 2 / 3) * fromℚ (+ 2 / 3)
    ≈⟨ *-cong (P-bernoulli-true 2 1) (P-bernoulli-true 2 1) ⟨
  biased ∙ (↑ id) * biased ∙ (↑ id)
    ≈⟨ ⊗-rect ⟨
  P ∙ Y ∎
  where open ≤-Reasoning Probability
