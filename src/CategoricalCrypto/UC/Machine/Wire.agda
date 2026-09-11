{-# OPTIONS --safe --without-K --guardedness #-}

-- Composing with a wire costs no trace.
--
-- `𝒢ₚ`'s composition is a ⊕-trace, but when one factor is a WIRE — a stateless
-- relabelling, which every structural morphism of the layer is — the loop is
-- solved generically by `GConstructionEmbedding`'s `absorbˡ`/`absorbʳ`: the
-- composite is the other factor with its interface renamed, same state.
-- `sandwichᴹ` is that shape, and the two absorption lemmas are what let a
-- statement about a structural composite be proved by case analysis on a sum
-- instead of by unrolling `iter`.
--
-- The embedding's lemmas are applied through their QUALIFIED names rather than
-- by instantiating `Embed.WithTrace` as a module: a module application copies
-- every sibling, and those siblings' types mention the trace
-- (`docs/stduc-supersession-plan.md` §1.1 measures the difference at 8 GiB).

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Monoidal.Distributive as MD
import Categories.GConstructionEmbedding as GE

open import Data.Product.Base using (_,_)
open import Data.Sum.Base as Sum using (_⊎_)
open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pure using (pure-idᵏ; +₁-pureᵏ)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary using (wire-⌜⌝)

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Tensor.Structural as Struct
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Naturality as Nat

module CategoricalCrypto.UC.Machine.Wire where

-- Re-exported: `UC.Machine.Slide` reaches `sandwichᴹ`/`sandwich-∘` through
-- its bare `open import … Wire`.
open import CategoricalCrypto.Machines.Sandwich public

private
  module ℳ = SymmetricMonoidalCategory (ℳₚ 0ℓ)
  module 𝒱 = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ
  module 𝒢 = Category (𝒢ₚ 0ℓ)
  module MT = Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module MN = Nat (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module R = MT.Remaining (Remainingₚ 0ℓ)

open Core (𝒱ₚ 0ℓ)
open KD (Dₚ-DiscreteMonad {0ℓ}) using (pureᵏ)
open MD.MonoidalDistributive (distₚ 0ℓ) using (_+₁_)
open MCat (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ) using (∘ᴹ-resp-≈ᴹ)
open Sim (𝒱ₚ 0ℓ)  (𝒫ₚ 0ℓ)
open Struct (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) using (⊗ᵉ-pureˡ; ⊗ᵉ-pureʳ)
open Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- Absorption

private
  -- Read at the four trace laws `𝒢ₚ` itself was built from, so that the
  -- `_∘_` in the statement is `𝒢ₚ`'s.
  absorbˡᵂ : {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : Set}
             {u : Machine B⁺ D⁺} {v : Machine D⁻ B⁻} {g : Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)}
           → 𝒢._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {D⁺ , D⁻} (σᴹ ∘ᴹ (u ⊗ᵉ v)) g
             ≈ᴹ ((idᴹ ⊗ᵉ u) ∘ᴹ (g ∘ᴹ (idᴹ ⊗ᵉ v)))
  absorbˡᵂ = GE.Embed.WithTrace.absorbˡ ℳ.U ℳ.monoidal (Tracedₚ 0ℓ)
               R.trace-resp-≈ᴹ (MN.trace-∘ˡ _ _) (MN.trace-∘ʳ _ _) (R.trace-comm _)

  absorbʳᵂ : {A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ : Set}
             {p : Machine A⁺ B⁺} {q : Machine B⁻ A⁻} {f : Machine (B⁺ ⊎ D⁻) (B⁻ ⊎ D⁺)}
           → 𝒢._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {D⁺ , D⁻} f (σᴹ ∘ᴹ (p ⊗ᵉ q))
             ≈ᴹ ((q ⊗ᵉ idᴹ) ∘ᴹ (f ∘ᴹ (p ⊗ᵉ idᴹ)))
  absorbʳᵂ = GE.Embed.WithTrace.absorbʳ ℳ.U ℳ.monoidal (Tracedₚ 0ℓ)
               R.trace-resp-≈ᴹ (MN.trace-∘ˡ _ _) (MN.trace-∘ʳ _ _) (R.trace-comm _)

  -- `id +₁ pureᵏ h` and `pureᵏ h +₁ id`, as functions.
  idˡ-pure : {V W V′ : Set} (h : V → W) → 𝒱._≈_ (𝒱.id {V′} +₁ pureᵏ h) (pureᵏ (Sum.map (λ v → v) h))
  idˡ-pure h = +₁-pureᵏ pure-idᵏ (𝒱.Equiv.refl {x = pureᵏ h})

  idʳ-pure : {V W V′ : Set} (h : V → W) → 𝒱._≈_ (pureᵏ h +₁ 𝒱.id {V′}) (pureᵏ (Sum.map h (λ v → v)))
  idʳ-pure h = +₁-pureᵏ (𝒱.Equiv.refl {x = pureᵏ h}) pure-idᵏ

------------------------------------------------------------------------
-- Composing with a wire

module _ {A B C : Iface} (up : Pos B → Pos C) (down : Neg C → Neg B) where

  wire-∘ᴹ : (f : Proc A B)
          → 𝒫._≈_ {A} {C} (wireᴹ up down 𝒫.∘ f)
              (sandwichᴹ f (Sum.map (λ a → a) down) (Sum.map (λ a → a) up))
  wire-∘ᴹ f =
       𝒫.∘-resp-≈ˡ {f = wireᴹ up down} (wire-⌜⌝ up down)
    ○ᴹ absorbˡᵂ
    ○ᴹ ∘ᴹ-resp-≈ᴹ (≲⇒≈ᴹ (⊗ᵉ-pureˡ (pureᵏ up)))
                  (∘ᴹ-resp-≈ᴹ reflᴹ (≲⇒≈ᴹ (⊗ᵉ-pureˡ (pureᵏ down))))
    ○ᴹ ∘ᴹ-resp-≈ᴹ reflᴹ (≲⇒≈ᴹ (pure-∘ʳ (𝒱.id +₁ pureᵏ down) f))
    ○ᴹ ≲⇒≈ᴹ (pure-∘ˡ (𝒱.id +₁ pureᵏ up) _)
    ○ᴹ squeeze f _ _ (idˡ-pure down) (idˡ-pure up)

module _ {A B C : Iface} (up : Pos A → Pos B) (down : Neg B → Neg A) where

  ∘-wireᴹ : (f : Proc B C)
          → 𝒫._≈_ {A} {C} (f 𝒫.∘ wireᴹ up down)
              (sandwichᴹ f (Sum.map up (λ a → a)) (Sum.map down (λ a → a)))
  ∘-wireᴹ f =
       𝒫.∘-resp-≈ʳ {f = wireᴹ up down} (wire-⌜⌝ up down)
    ○ᴹ absorbʳᵂ
    ○ᴹ ∘ᴹ-resp-≈ᴹ (≲⇒≈ᴹ (⊗ᵉ-pureʳ (pureᵏ down)))
                  (∘ᴹ-resp-≈ᴹ reflᴹ (≲⇒≈ᴹ (⊗ᵉ-pureʳ (pureᵏ up))))
    ○ᴹ ∘ᴹ-resp-≈ᴹ reflᴹ (≲⇒≈ᴹ (pure-∘ʳ (pureᵏ up +₁ 𝒱.id) f))
    ○ᴹ ≲⇒≈ᴹ (pure-∘ˡ (pureᵏ down +₁ 𝒱.id) _)
    ○ᴹ squeeze f _ _ (idʳ-pure up) (idʳ-pure down)
