{-# OPTIONS --safe --without-K #-}

-- The G construction's two operations, laxly.
--
-- A G-composite is a trace of an interface tensor between two pure wiring legs
-- and a G-tensor is an interface tensor between two copies of the middle-four
-- interchange, so both congruences are `Machines.Sim.Lax`'s three applied with
-- the structural legs strict.  Nothing here reads a machine.

open import Categories.Category using (Category; _[_,_]; _[_∘_])
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
import Categories.Category.Monoidal.Distributive as MD
import Categories.GConstruction as GC
import Categories.GConstructionMonoidal as GM

open import Data.Product.Base using (_×_)

import CategoricalCrypto.Machines.Bundle as Bundle
import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.G as G
import CategoricalCrypto.Machines.Iteration as Iteration
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Sim.Lax as Lax

module CategoricalCrypto.Machines.G.Lax
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱)
  (E : Iteration.Elgot 𝒱 dist 𝒫) where

open Bundle 𝒱 dist 𝒫
open G 𝒱 dist 𝒫 E
open Lax 𝒱 dist 𝒫 E
open MCat 𝒱 𝒫
open Sim 𝒱 𝒫
open SymmetricMonoidalCategory 𝒱
open HomReasoning

private
  module 𝔾 = MonoidalCategory Mealy-Gᴹ

  rawᴳ = GC.composeᴳ-raw Mealy-Category Mealy-Monoidal Mealy-Traced

private variable
  A B C D : Obj × Obj
  σ τ : unit ⇒ unit

-- The two structural legs and the interchange are strict, so they contribute
-- the identity scalar, which is what the composite's scalar is read back to.
private
  trivial : id ∘ ((σ ∘ τ) ∘ id) ≈ σ ∘ τ
  trivial = identityˡ ○ identityʳ

∘ᴳ-resp-≈ˡ : {g g′ : 𝔾.U [ B , C ]} {f f′ : 𝔾.U [ A , B ]}
           → g ≈ˡ[ σ ] g′ → f ≈ˡ[ τ ] f′
           → 𝔾.U [ g ∘ f ] ≈ˡ[ σ ∘ τ ] 𝔾.U [ g′ ∘ f′ ]
∘ᴳ-resp-≈ˡ u v = ≈ˡ-resp-scalar trivial
  (≈ˡ-congˡ rawᴳ
    (≈ˡ-congʳ (trace-resp-≈ˡ
                (∘ᴹ-resp-≈ˡ ≈ˡ-refl (∘ᴹ-resp-≈ˡ (⊗ᵉ-resp-≈ˡ u v) ≈ˡ-refl)))
              (⟺ᴹ rawᴳ)))

opaque
  unfolding GM._⊗₁ᴳ_

  ⊗₁ᴳ-resp-≈ˡ : {g g′ : 𝔾.U [ A , B ]} {f f′ : 𝔾.U [ C , D ]}
              → g ≈ˡ[ σ ] g′ → f ≈ˡ[ τ ] f′
              → 𝔾._⊗₁_ g f ≈ˡ[ σ ∘ τ ] 𝔾._⊗₁_ g′ f′
  ⊗₁ᴳ-resp-≈ˡ u v = ≈ˡ-resp-scalar trivial
    (∘ᴹ-resp-≈ˡ ≈ˡ-refl (∘ᴹ-resp-≈ˡ (⊗ᵉ-resp-≈ˡ u v) ≈ˡ-refl))
