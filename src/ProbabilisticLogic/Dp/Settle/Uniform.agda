{-# OPTIONS --safe --without-K --guardedness #-}

-- The uniform cascade settles on the uniform distribution: `Dp.Uniform.uniformₚ`
-- halts after its `n` coins and scores `uniform-Vec n` exactly.  A machine that
-- samples in `Dₚ` without going through a protocol image — a lazily sampled
-- oracle, say — needs this to be read as a `Dist-ℚ` kernel.

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Vec.Base using ([]; _∷_)

open import ProbabilisticLogic.Distribution.RationalDist using (Dmap; return-ℚ)
open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool; uniform-Vec)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin using (coinₚ)
open import ProbabilisticLogic.Dp.Settle
open import ProbabilisticLogic.Dp.Uniform using (uniformₚ)

module ProbabilisticLogic.Dp.Settle.Uniform where

uniformₚ-settles : (n : ℕ) → Σ[ i ∈ ℕ ] Settlesᵀ i (uniformₚ n) (uniform-Vec n)
uniformₚ-settles zero    = 1 , Settlesᵀ-return []
uniformₚ-settles (suc n) =
  Settlesᵀ-bind⋆ 2 (coinₚ uniform-Bool) (λ b → mapₚ (b ∷_) (uniformₚ n))
                 uniform-Bool (λ b → Dmap (b ∷_) (uniform-Vec n))
                 (Settlesᵀ-coin uniform-Bool)
    λ b → Settlesᵀ-bind⋆ (proj₁ (uniformₚ-settles n)) (uniformₚ n) (λ v → returnₚ (b ∷ v))
                         (uniform-Vec n) (λ v → return-ℚ (b ∷ v))
                         (proj₂ (uniformₚ-settles n)) λ v → 1 , Settlesᵀ-return (b ∷ v)
