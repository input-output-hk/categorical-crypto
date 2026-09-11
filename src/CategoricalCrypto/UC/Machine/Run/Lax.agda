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
-- The induction is repeated rather than shared: `UC.Machine.Run`'s helpers are
-- parameterized by a `_≲_`, whose `θ-discard` a lax simulation deliberately
-- does not carry, and re-presenting a lax one as a strict one would change the
-- two machines' state records and so the very `runᴹFrom` being compared.

open import Categories.Category.Monoidal.Bundle

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine.Run using (Closed)

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

    padϕ : {Z : Set} → MC.St f × Z → Dₚ (MC.St g × Z)
    padϕ p = returnₚ (ϕ (proj₁ p) , proj₂ p)

    pad-fn : {Z : Set} (p : MC.St f × Z) → (L.θˡ l V.⊗₁ V.id) p ≈ₚ padϕ p
    pad-fn (s , z) = bindˣ (P.is-fn (L.θˡ-pure l) s)
               ⟨≈⟩ >>=ₚ-identityˡ (ϕ s) _
               ⟨≈⟩ >>=ₚ-identityˡ z _

    step-lax : (p : MC.St f × (⊥ ⊎ Neg B))
             → (MC.step f p >>=ₚ padϕ) ≈ₚ MC.step g (ϕ (proj₁ p) , proj₂ p)
    step-lax p = bindᶠ (λ q → ≈sym (pad-fn q))
           ⟨≈⟩ L.θˡ-step l p
           ⟨≈⟩ bindˣ (pad-fn p)
           ⟨≈⟩ >>=ₚ-identityˡ (ϕ (proj₁ p) , proj₂ p) (MC.step g)

    contᵍ : (Pos B → Strat (Neg B) (Pos B)) → MC.St g → Pos B → Dₚ Bool
    contᵍ k m′ r = runᴹFrom g m′ (k r)

    resume-lax : {cᶠ : MC.St f → Pos B → Dₚ Bool} {cᵍ : MC.St g → Pos B → Dₚ Bool}
               → ((m′ : MC.St f) (r : Pos B) → cᶠ m′ r ≈ₚ cᵍ (ϕ m′) r)
               → (p : MC.St f × (⊥ ⊎ Pos B))
               → resumeᴹ f cᶠ p ≈ₚ resumeᴹ g cᵍ (ϕ (proj₁ p) , proj₂ p)
    resume-lax h (_  , inj₁ a) = ⊥-elim a
    resume-lax h (m′ , inj₂ r) = h m′ r

    runFrom-lax : (m : MC.St f) (d : Strat (Neg B) (Pos B))
                → runᴹFrom f m d ≈ₚ runᴹFrom g (ϕ m) d
    runFrom-lax m (out b)    = ≈refl
    runFrom-lax m (coin μ k) = bindᶠ (λ b → runFrom-lax m (k b))
    runFrom-lax m (ask q k)  =
        bindᶠ (resume-lax {cᵍ = contᵍ k} (λ m′ r → runFrom-lax m′ (k r)))
      ⟨≈⟩ ≈sym (bindᶠ (λ p → >>=ₚ-identityˡ (ϕ (proj₁ p) , proj₂ p)
                                            (resumeᴹ g (contᵍ k))))
      ⟨≈⟩ ≈sym (>>=ₚ-assoc (MC.step f (m , inj₂ q)) padϕ (resumeᴹ g (contᵍ k)))
      ⟨≈⟩ bindˣ (step-lax (m , inj₂ q))

    point-lax : mapₚ ϕ (MC.point (MC.state f) tt)
              ≈ₚ (σ tt >>=ₚ λ _ → MC.point (MC.state g) tt)
    point-lax = bindᶠ (λ s → ≈sym (P.is-fn (L.θˡ-pure l) s)) ⟨≈⟩ L.θˡ-point l tt

  run-lax : (d : Strat (Neg B) (Pos B)) → runᴹ f d ≈ₚ (σ tt >>=ₚ λ _ → runᴹ g d)
  run-lax d = bindᶠ (λ m → runFrom-lax m d)
        ⟨≈⟩ ≈sym (bind-map (MC.point (MC.state f) tt) ϕ (λ m → runᴹFrom g m d))
        ⟨≈⟩ bindˣ point-lax
        ⟨≈⟩ >>=ₚ-assoc (σ tt) _ _
