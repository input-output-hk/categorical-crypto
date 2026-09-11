{-# OPTIONS --safe --without-K --guardedness #-}

-- What a lax simulation does to a closed run: it prefixes it.
--
-- `UC.Machine.Run` is the strict half — there the state map is spent one step
-- at a time and the two runs come out EQUAL.  A lax simulation differs from a
-- strict one only at the point, which the step-level induction never touches,
-- so the same induction leaves the prefix standing in front of the simulated
-- run.  Turning that into an ε-agreement is `Dp.Mass.astotal-bind`, and the
-- consumer applies it (`UC.Seam.Grounding.Prefix`).
--
-- The induction itself is shared, not repeated: `UC.Machine.Run.runFrom-ϕ` is
-- parameterized by the state map and its step law rather than by a `_≲_`,
-- whose `θ-discard` a lax simulation deliberately does not carry.  Sharing
-- over the SIMULATION would not work — re-presenting a lax one as a strict one
-- would change the two machines' state records and so the very `runᴹFrom`
-- being compared — so only the pair the induction actually spends is shared.

open import Categories.Category.Monoidal.Bundle

open import Data.Empty using (⊥)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine.Run using (Closed; padϕ; runFrom-ϕ)

import Categories.Category.Kleisli.Discrete.Pure as KDP
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

    pad-fn : {Z : Set} (p : MC.St f × Z) → (L.θˡ l V.⊗₁ V.id) p ≈ₚ padϕ ϕ p
    pad-fn (s , z) = bindˣ (P.is-fn (L.θˡ-pure l) s)
               ⟨≈⟩ >>=ₚ-identityˡ (ϕ s) _
               ⟨≈⟩ >>=ₚ-identityˡ z _

    step-lax : (p : MC.St f × (⊥ ⊎ Neg B))
             → (MC.step f p >>=ₚ padϕ ϕ) ≈ₚ MC.step g (ϕ (proj₁ p) , proj₂ p)
    step-lax p = bindᶠ (λ q → ≈sym (pad-fn q))
           ⟨≈⟩ L.θˡ-step l p
           ⟨≈⟩ bindˣ (pad-fn p)
           ⟨≈⟩ >>=ₚ-identityˡ (ϕ (proj₁ p) , proj₂ p) (MC.step g)

    runFrom-lax : (m : MC.St f) (d : Strat (Neg B) (Pos B))
                → runᴹFrom f m d ≈ₚ runᴹFrom g (ϕ m) d
    runFrom-lax = runFrom-ϕ ϕ step-lax

    point-lax : mapₚ ϕ (MC.point (MC.state f) tt)
              ≈ₚ (σ tt >>=ₚ λ _ → MC.point (MC.state g) tt)
    point-lax = bindᶠ (λ s → ≈sym (P.is-fn (L.θˡ-pure l) s)) ⟨≈⟩ L.θˡ-point l tt

  run-lax : (d : Strat (Neg B) (Pos B)) → runᴹ f d ≈ₚ (σ tt >>=ₚ λ _ → runᴹ g d)
  run-lax d = bindᶠ (λ m → runFrom-lax m d)
        ⟨≈⟩ ≈sym (bind-map (MC.point (MC.state f) tt) ϕ (λ m → runᴹFrom g m d))
        ⟨≈⟩ bindˣ point-lax
        ⟨≈⟩ >>=ₚ-assoc (σ tt) _ _
