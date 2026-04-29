{-# OPTIONS --safe --without-K #-}

module ProbabilisticLogic where

open import ProbabilisticLogic.Abstract  public
open import ProbabilisticLogic.Reasoning public

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
