{-# OPTIONS --safe --without-K #-}

-- `traceᴹ` respects simulation.  This is the ⊕-trace law the layer's
-- axiom-freeness turns on, and the reason the hom equality is a simulation: the
-- two loops being related run at two different state objects, and the only
-- thing that can carry one to the other is uniformity along the map between
-- them — `iter-uniform` at the simulation's own `𝒫`-map.
--
-- Everything outside the loop is `pad-transport`: a state map commutes with an
-- action on the interface alone.

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Pure using (PureSub)
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Iteration as Iteration
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Trace as Trace

module CategoricalCrypto.Machines.Trace.Congruence
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱)
  (E : Iteration.Elgot 𝒱 dist 𝒫) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open Equiv
open Frame 𝒱
open Iteration 𝒱 dist 𝒫 using (pad)
open Iteration.Elgot E
open MD.MonoidalDistributive dist
open MDP 𝒱 dist
open PureSub 𝒫
open Sim 𝒱 𝒫
open Trace 𝒱 dist 𝒫 E

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

module _ (S T : State) (A B X : Obj)
  {k : obj S ⊗₀ (A + X) ⇒ obj S ⊗₀ (B + X)} {k′ : obj T ⊗₀ (A + X) ⇒ obj T ⊗₀ (B + X)}
  (θ : obj S ⇒ obj T) (θᵖ : Pure θ) (θˢ : pad θ ∘ k ≈ k′ ∘ pad θ) where

  private
    loop-sim : loopBody T A B X k′ ∘ pad θ ≈ pad θ ∘ loopBody S A B X k
    loop-sim = assoc ○ (refl⟩∘⟨ pad-transport θ (i₂ {A} {X})) ○ sym-assoc
             ○ (⟺ θˢ ⟩∘⟨refl) ○ assoc

  solve-sim : pad θ ∘ solve S A B X k ≈ solve T A B X k′ ∘ pad θ
  solve-sim = δ-unique branch₁ branch₂
    where
      branch₁ = (pullʳ (solve-i₁ S A B X k) ○ identityʳ)
              ○ ⟺ (pullʳ (⟺ (pad-transport θ i₁))
                   ○ pullˡ (solve-i₁ T A B X k′) ○ identityˡ)

      branch₂ = pullʳ (solve-i₂ S A B X k)
              ○ ⟺ (iter-uniform θ θᵖ loop-sim)
              ○ ⟺ (pullʳ (⟺ (pad-transport θ i₂)) ○ pullˡ (solve-i₂ T A B X k′))

  traceStep-sim : pad θ ∘ traceStep S A B X k ≈ traceStep T A B X k′ ∘ pad θ
  traceStep-sim = sym-assoc ○ (solve-sim ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ enter)
                ○ (refl⟩∘⟨ sym-assoc) ○ sym-assoc
    where
      enter : pad θ ∘ (k ∘ id ⊗₁ i₁) ≈ k′ ∘ (id ⊗₁ i₁ ∘ pad θ)
      enter = sym-assoc ○ (θˢ ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ ⟺ (pad-transport θ i₁))

trace-resp-≲ : {A B X : Obj} {f g : Machine (A + X) (B + X)}
             → f ≲ g → traceᴹ A B X f ≲ traceᴹ A B X g
trace-resp-≲ {A} {B} {X} {f} {g} s =
  sim (θ s) (θ-pure s) (θ-discard s) (θ-point s)
      (traceStep-sim (state f) (state g) A B X (θ s) (θ-pure s) (θ-step s))
