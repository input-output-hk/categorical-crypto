{-# OPTIONS --safe --without-K #-}

-- The probability vocabulary, in one import: carriers, the monad and its
-- equality, sub-probability, expectation, advantage, uniform sampling.
--
-- `Partial` is re-exported unrestricted because it carries the `Dist⊥`
-- instances, which instance resolution must see at every consumer.

module ProbabilisticLogic.Prelude where

open import ProbabilisticLogic.Distribution.RationalDist public using
  ( Dist-ℚ; entries; mass-1
  ; return-ℚ; _>>=ᴹ_; Dmap
  ; _≈Mℚ_
  ; >>=ᴹ-cong; >>=ᴹ-identityˡ; >>=ᴹ-assoc
  ; lookupᴰℚ; lookupᴰℚ-bind )

open import ProbabilisticLogic.Distribution.RationalDist.Partial public

open import ProbabilisticLogic.Distribution.RationalDist.Expectation public using
  ( E; mb; Pr₁; Pr₁-bind; Prᵇ⊥; Pr₁⊥; Pr₁⊥-just; Pr₁⊥-cong )

open import ProbabilisticLogic.Distribution.RationalDist.Setoid public using
  ( Mℚ-setoid; module Mℚ; >>=ᴹ-congˡ; >>=ᴹ-congʳ )

open import ProbabilisticLogic.Distribution.RationalDist.Advantage public using
  ( advᵇ⊥; advᵇ⊥-just; adv⊥; adv⊥-sym; adv⊥-triangle; adv⊥-≈⇒0 )

open import ProbabilisticLogic.Distribution.Uniform public using
  ( bool→ℚ; indᵇ; δ; fromℕ; inv-pow-2; uniform-Bool; uniform-Vec )
