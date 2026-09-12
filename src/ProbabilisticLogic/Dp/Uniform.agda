{-# OPTIONS --safe --without-K --guardedness #-}

-- A uniform bit vector in the delay monad: `Protocol.uniformVec`'s cascade one
-- layer down, one fair `coinₚ` per bit.  A machine that samples without going
-- through a protocol image needs the distribution here rather than as a call
-- tree.

open import Data.Bool.Base using (Bool)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)

open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin using (coinₚ)

module ProbabilisticLogic.Dp.Uniform where

uniformₚ : (n : ℕ) → Dₚ (Vec Bool n)
uniformₚ zero    = returnₚ []
uniformₚ (suc n) = coinₚ uniform-Bool >>=ₚ λ b → mapₚ (b ∷_) (uniformₚ n)
