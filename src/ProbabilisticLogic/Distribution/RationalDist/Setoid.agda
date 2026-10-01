{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude

open import Relation.Binary

open import ProbabilisticLogic.Distribution.RationalDist

module ProbabilisticLogic.Distribution.RationalDist.Setoid where

private variable
  ℓ : Level
  A B : Type ℓ

-- `_≈Mℚ_` bundled for reasoning chains.  It mentions only `entries`, so an
-- INFERRED intermediate distribution leaves `mass-1` a stray meta: chains must
-- name their intermediates.
Mℚ-setoid : (A : Type ℓ) → Setoid _ _
Mℚ-setoid A = record { Carrier = Dist-ℚ A ; _≈_ = _≈Mℚ_ ; isEquivalence = ≈Mℚ-isEquivalence }

module Mℚ {ℓ} {A : Type ℓ} = Setoid (Mℚ-setoid A)

-- Bind congruences with the reflexive side PINNED explicitly.  Inside a
-- reasoning chain the "to" endpoint is a metavariable while the proof is
-- checked, so a bare `(λ P → refl)` under an inferred `{μ}`/`{f}` makes Agda
-- solve the distribution meta by inverting `_+ℚ_` — a heap blow-up.
>>=ᴹ-congˡ : (μ : Dist-ℚ A) (f g : A → Dist-ℚ B)
           → (∀ a → f a ≈Mℚ g a) → (μ >>=ᴹ f) ≈Mℚ (μ >>=ᴹ g)
>>=ᴹ-congˡ μ f g pt = >>=ᴹ-cong {μ = μ} {μ} {f} {g} (λ P → refl) pt

>>=ᴹ-congʳ : (K : A → Dist-ℚ B) (μ ν : Dist-ℚ A) → μ ≈Mℚ ν → (μ >>=ᴹ K) ≈Mℚ (ν >>=ᴹ K)
>>=ᴹ-congʳ K μ ν e = >>=ᴹ-cong {μ = μ} {ν} {K} {K} e (λ a → Mℚ.refl {x = K a})
