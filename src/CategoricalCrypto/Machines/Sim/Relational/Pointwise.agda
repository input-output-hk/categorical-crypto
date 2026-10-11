{-# OPTIONS --safe --without-K --guardedness #-}

-- `Machines.Sim.Relational` at `Kl(Dₚ)`, read at a point: a simulation along
-- interface FUNCTIONS is two pointwise laws (`Machines.Pointwise.simFn` with a
-- map on each letter).  A relational simulation's coupling is then the apex's
-- own point and step, and these laws are its two marginals.

module CategoricalCrypto.Machines.Sim.Relational.Pointwise where

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (module MC; module V; module K; module KP)

import CategoricalCrypto.Machines.Sim.Relational as Relational

module RS = Relational (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)

private
  variable X X′ Y Y′ : Set

simFn[] : {S T : MC.State} {k : MC.obj S × X → Dₚ (MC.obj S × Y)}
          {k′ : MC.obj T × X′ → Dₚ (MC.obj T × Y′)} (h : MC.obj S → MC.obj T) (μ : X → X′) (ν : Y → Y′)
        → ((x : V.unit) → (MC.point S x >>=ₚ λ s → returnₚ (h s)) ≈ₚ MC.point T x)
        → ((p : MC.obj S × X) → (k p >>=ₚ λ r → returnₚ (h (proj₁ r) , ν (proj₂ r)))
                                ≈ₚ k′ (h (proj₁ p) , μ (proj₂ p)))
        → MC.mk S k RS.≲[ K.pureᵏ μ ∣ K.pureᵏ ν ] MC.mk T k′
simFn[] {k′ = k′} h μ ν hp hs = record
  { leg       = K.pureᵏ h
  ; leg-pure  = KP.structural h
  ; leg-point = hp
  ; leg-step  = λ p → bindᶠ (K.pureᵏ-⊗ h ν) ⟨≈⟩ hs p
              ⟨≈⟩ ≈sym (bindˣ (K.pureᵏ-⊗ h μ p) ⟨≈⟩ >>=ₚ-identityˡ (h (proj₁ p) , μ (proj₂ p)) k′)
  }
