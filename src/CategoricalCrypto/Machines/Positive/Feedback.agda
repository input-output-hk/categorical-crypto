{-# OPTIONS --safe --without-K --guardedness #-}

-- Process feedback is deterministic port retagging followed by the actual
-- Mealy/Elgot trace.  Its observable executions are finite positive paths;
-- this operation does not add an infinite-path or refusal observation.
module CategoricalCrypto.Machines.Positive.Feedback where

open import Data.Sum.Base
open import Data.Product.Base
open import Data.Unit.Polymorphic.Base using (tt)
open import Level
open import Relation.Binary.PropositionalEquality using (refl)
import Relation.Binary.Construct.Closure.Equivalence as EqC
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning
import CategoricalCrypto.Machines.Base as PM
import CategoricalCrypto.Machines.Trace.Congruence as TraceCong
import CategoricalCrypto.Machines.Pointwise as OldPoint
import CategoricalCrypto.Machines.Sandwich as Old
import CategoricalCrypto.Machines.Positive.Pointwise as Point
import CategoricalCrypto.Machines.Positive.Repack as Re

private
  module R = Re.At 0ℓ
  module PTC = TraceCong (PM.𝒱ₚ 0ℓ) (PM.distₚ 0ℓ) (PM.𝒫ₚ 0ℓ) (PM.Elgotₚ 0ℓ)
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

module _ {U V U′ V′ : Set} (i : U′ → U) (o : V → V′) where
  module _ {f g : R.P.Machine U V} (sim : f R.PS.≲ g) where
    private
      h = OldPoint.KP.fn (R.PS.θ-pure sim)

    old-sandwich-sim : Old.sandwichᴹ f i o R.PS.≲ Old.sandwichᴹ g i o
    old-sandwich-sim = OldPoint.simFn h
      (λ { tt → bindᶠ (λ s → ≈sym (OldPoint.KP.is-fn (R.PS.θ-pure sim) s))
        ⟨≈⟩ R.PS.θ-point sim tt }) λ p →
      map-fuse (R.P.step f (proj₁ p , i (proj₂ p)))
        (λ z → proj₁ z , o (proj₂ z)) (λ z → h (proj₁ z) , proj₂ z)
        (λ z → h (proj₁ z) , o (proj₂ z)) (λ _ → refl)
      ⟨≈⟩ ≈sym (map-fuse (R.P.step f (proj₁ p , i (proj₂ p)))
        (λ z → h (proj₁ z) , proj₂ z) (λ z → proj₁ z , o (proj₂ z))
        (λ z → h (proj₁ z) , o (proj₂ z)) (λ _ → refl))
      ⟨≈⟩ map-arg (λ z → proj₁ z , o (proj₂ z))
        (OldPoint.fnStep (R.PS.θ-pure sim) (R.PS.θ-step sim) (proj₁ p , i (proj₂ p)))

  old-sandwich-resp : {f g : R.P.Machine U V} → f R.PS.≈ᴹ g
    → Old.sandwichᴹ f i o R.PS.≈ᴹ Old.sandwichᴹ g i o
  old-sandwich-resp = EqC.gmap (λ f → Old.sandwichᴹ f i o) old-sandwich-sim

opaque
  unfolding feedbackₚ

  feedbackₚ-resp : {f g : R.P.Machine ((A⁺ ⊎ C⁺) ⊎ (B⁻ ⊎ C⁻)) ((A⁻ ⊎ C⁻) ⊎ (B⁺ ⊎ C⁺))}
    → f R.PS.≈ᴹ g → feedbackₚ f R.PS.≈ᴹ feedbackₚ g
  feedbackₚ-resp p = PTC.trace-resp-≈ᴹ (old-sandwich-resp input output p)

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
