{-# OPTIONS --safe --without-K --guardedness #-}

-- What a lax simulation does to a closed run: it prefixes it with `σ`.  The
-- simulation is lax only at the point, which `UC.Machine.Run.runFrom-ϕ` never
-- touches; `Dp.Mass.astotal-bind` turns the prefix into an ε-agreement when
-- `σ` is almost surely total.

open import Categories.Category.Monoidal.Bundle

open import Data.Product.Base
open import Data.Unit.Polymorphic.Base
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (fnStep)
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine.Run using (runFrom-ϕ)

import Categories.Category.Construction.Kleisli.Discrete.Pure as KDP
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim.Lax as Lax

module CategoricalCrypto.UC.Machine.Run.Lax where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module P  = KDP (Dₚ-DiscreteMonad {0ℓ})
  module L  = Lax (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module V  = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)

module _ {B : Iface} {σ : V.unit V.⇒ V.unit} {f g : Closed B}
         (l : f L.≲ˡ[ σ ] g) where

  private
    ϕ : MC.St f → MC.St g
    ϕ = P.fn (L.θˡ-pure l)

    runFrom-lax : (m : MC.St f) (d : Strat (Neg B) (Pos B))
                → runᴹFrom f m d ≈ₚ runᴹFrom g (ϕ m) d
    runFrom-lax = runFrom-ϕ ϕ (fnStep (L.θˡ-pure l) (L.θˡ-step l))

    point-lax : mapₚ ϕ (MC.point (MC.state f) tt)
              ≈ₚ (σ tt >>=ₚ λ _ → MC.point (MC.state g) tt)
    point-lax = bindᶠ (λ s → ≈sym (P.is-fn (L.θˡ-pure l) s)) ⟨≈⟩ L.θˡ-point l tt

  run-lax : (d : Strat (Neg B) (Pos B)) → runᴹ f d ≈ₚ (σ tt >>=ₚ λ _ → runᴹ g d)
  run-lax d = bindᶠ (λ m → runFrom-lax m d)
        ⟨≈⟩ ≈sym (bind-map (MC.point (MC.state f) tt) ϕ (λ m → runᴹFrom g m d))
        ⟨≈⟩ bindˣ point-lax
        ⟨≈⟩ >>=ₚ-assoc (σ tt) _ _
