{-# OPTIONS --safe --without-K --guardedness #-}

-- Process feedback is deterministic port retagging followed by the actual
-- Mealy/Elgot trace.  Its observable executions are finite positive paths;
-- this operation does not add an infinite-path or refusal observation.
module CategoricalCrypto.Machines.Positive.Feedback where

open import Data.Sum.Base
open import Level
import CategoricalCrypto.Machines.Sandwich as Old
import CategoricalCrypto.Machines.Positive.Pointwise as Point
import CategoricalCrypto.Machines.Positive.Repack as Re

private
  module R = Re.At 0ℓ
  variable A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Set

input : (A⁺ ⊎ B⁻) ⊎ (C⁻ ⊎ C⁺) → (A⁺ ⊎ C⁺) ⊎ (B⁻ ⊎ C⁻)
input (inj₁ (inj₁ a)) = inj₁ (inj₁ a)
input (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
input (inj₂ (inj₁ c)) = inj₂ (inj₂ c)
input (inj₂ (inj₂ c)) = inj₁ (inj₂ c)

output : (A⁻ ⊎ C⁻) ⊎ (B⁺ ⊎ C⁺) → (A⁻ ⊎ B⁺) ⊎ (C⁻ ⊎ C⁺)
output (inj₁ (inj₁ a)) = inj₁ (inj₁ a)
output (inj₁ (inj₂ c)) = inj₂ (inj₁ c)
output (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
output (inj₂ (inj₂ c)) = inj₂ (inj₂ c)

opaque
  feedbackₚ : R.P.Machine ((A⁺ ⊎ C⁺) ⊎ (B⁻ ⊎ C⁻)) ((A⁻ ⊎ C⁻) ⊎ (B⁺ ⊎ C⁺))
            → R.P.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)
  feedbackₚ f = R.PTr.traceᴹ _ _ _ (Old.sandwichᴹ f input output)

  feedback₊ : R.Q.Machine ((A⁺ ⊎ C⁺) ⊎ (B⁻ ⊎ C⁻)) ((A⁻ ⊎ C⁻) ⊎ (B⁺ ⊎ C⁺))
            → R.Q.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)
  feedback₊ f = R.QTr.traceᴹ _ _ _ (Point.sandwichᴹ f input output)

repack-sandwich : {X Y X′ Y′ : Set} (f : R.P.Machine X Y) (i : X′ → X) (o : Y → Y′)
  → R.repack (Old.sandwichᴹ f i o) R.QS.≈ᴹ Point.sandwichᴹ (R.repack f) i o
repack-sandwich f i o = R.QS.reflᴹ

opaque
  unfolding feedback₊

  feedback-resp : {f g : R.Q.Machine ((A⁺ ⊎ C⁺) ⊎ (B⁻ ⊎ C⁻)) ((A⁻ ⊎ C⁻) ⊎ (B⁺ ⊎ C⁺))}
    → f R.QS.≈ᴹ g → feedback₊ f R.QS.≈ᴹ feedback₊ g
  feedback-resp p = R.QTC.trace-resp-≈ᴹ (Point.sandwich-resp input output p)

opaque
  unfolding feedbackₚ feedback₊

  repack-feedback : (f : R.P.Machine ((A⁺ ⊎ C⁺) ⊎ (B⁻ ⊎ C⁻)) ((A⁻ ⊎ C⁻) ⊎ (B⁺ ⊎ C⁺)))
    → R.repack (feedbackₚ f) R.QS.≈ᴹ feedback₊ (R.repack f)
  repack-feedback f = R.QS._○ᴹ_ (R.repack-trace (Old.sandwichᴹ f input output))
    (R.QTC.trace-resp-≈ᴹ (repack-sandwich f input output))
