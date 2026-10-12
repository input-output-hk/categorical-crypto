{-# OPTIONS --safe --without-K --guardedness #-}

-- CLC Lemmas 24–25 fix the process and attacker before choosing the
-- approximation errors ν₁,ν₂. A common symbolic experiment need not give
-- a single negligible slack for honest programs of unbounded size.
module CategoricalCrypto.Symbolic.Soundness.Errors where

open import Data.Bool.Base
open import Data.Nat.Base hiding (_⊔_; compare)
open import Data.Product
open import Data.Rational as ℚ using (ℚ)
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Machine using (Approximationᴹ)

import CategoricalCrypto.UC.Approximate.Local as Local

record ProtocolError {p e} (Protocol : Set p) (Eligible : Protocol → Set e)
  (actual predicted : Protocol → ℕ → Dₚ Bool) : Set (p ⊔ e) where
  field
    error : Protocol → ℕ → ℚ
    negligible-error : (f : Protocol) → Eligible f → Negligible (error f)
    realizes : (f : Protocol) → Eligible f → (η : ℕ)
      → actual f η ≈ₚ[ error f η ] predicted f η

module Comparison {p e} {Protocol : Set p} {Eligible : Protocol → Set e}
  {actual predicted : Protocol → ℕ → Dₚ Bool}
  (approximation : ProtocolError Protocol Eligible actual predicted) where
  private module Observation = Local Approximationᴹ ℕ (λ η → η)
  open ProtocolError approximation

  compare-at : (f g : Protocol) → Eligible f → Eligible g
    → ((η : ℕ) → predicted f η ≈ₚ predicted g η) → (η : ℕ)
    → actual f η ≈ₚ[ error f η ℚ.+ error g η ] actual g η
  compare-at f g sf sg agree η = ≈ₚ[]-trans
    (≈ₚ[]-resp (≈ₚ-refl _) (agree η) (realizes f sf η))
    (≈ₚ[]-sym (realizes g sg η))

  compare : (f g : Protocol) → Eligible f → Eligible g
    → ((η : ℕ) → predicted f η ≈ₚ predicted g η) → actual f Observation.∼ᴺ actual g
  compare f g sf sg agree = (λ η → error f η ℚ.+ error g η)
    , Negligible-+ (negligible-error f sf) (negligible-error g sg)
    , compare-at f g sf sg agree
