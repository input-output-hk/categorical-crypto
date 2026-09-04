{-# OPTIONS --safe --without-K #-}

-- The iteration hypothesis the machine layer's ⊕-trace needs, stated in the
-- base's own `_≈_` — nothing about machines is assumed.
--
-- Machines form a *feedback* category: one letter is consumed and one emitted
-- per step, so a loop message is only delivered on the next step.  Yanking
-- trivializes that delay, so a trace has to solve the loop *inside* one step —
-- unbounded Elgot iteration over the distributive `+`, dispatching "emit
-- externally = exit" against "emit on the loop wire = continue".  `iter`'s
-- first factor is the context (the machine's state), threaded through every
-- pass; that threading is what collapses the delay.
--
-- `iter-uniform` is stated along an arbitrary `𝒫`-map, not along a state *iso*:
-- the iso form suffices for every state reconciliation the trace laws perform,
-- but the simulation equality's congruence for `traceᴹ` needs uniformity along
-- the simulation's own state map, which is not invertible.  `𝒫` is what makes
-- both inhabited at a Kleisli base, where an arbitrary hom is effectful and
-- iteration transfers along the pure homs only; `_≲_`'s state map is drawn from
-- the same class, so the congruence lines up.

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Pure using (PureSub)
import Categories.Category.Monoidal.Distributive as MD
open import Level using (levelOfTerm)

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.Machines.Iteration
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱 using (onR)
open MD.MonoidalDistributive dist
open PureSub 𝒫
open Tensor 𝒱 dist 𝒫 using (tstep)

private variable A B C P S T : Obj
private variable u v : S ⊗₀ A ⇒ S ⊗₀ (B + A)

-- A state map padded out to a machine interface: the shape every state
-- reconciliation in the layer takes.
pad : S ⇒ T → S ⊗₀ A ⇒ T ⊗₀ A
pad θ = θ ⊗₁ id

record Elgot : Set (levelOfTerm 𝒱) where
  field
    iter : (S ⊗₀ A ⇒ S ⊗₀ (B + A)) → S ⊗₀ A ⇒ S ⊗₀ B

    iter-cong : u ≈ v → iter u ≈ iter v

    -- Elgot's fixpoint: run one pass, then exit or recurse.
    iter-fix : iter u ≈ [ id , iter u ] ∘ δ⇐ ∘ u

    -- Naturality in the output.  `k` may act on the context as well, which is
    -- what makes this cover post-composition with a *stateful* machine; the
    -- loop branch of `tstep k id` leaves the context alone, so the extra
    -- generality costs nothing.
    iter-out : (k : S ⊗₀ B ⇒ S ⊗₀ C) → k ∘ iter u ≈ iter (tstep k id ∘ u)

    -- Superposing: a context factor the body never touches passes through.
    iter-ctx : iter (onR {P = P} u) ≈ onR (iter u)

    iter-uniform : (θ : S ⇒ T) → Pure θ → {v : T ⊗₀ A ⇒ T ⊗₀ (B + A)}
                 → v ∘ pad θ ≈ pad θ ∘ u → iter v ∘ pad θ ≈ pad θ ∘ iter u

    -- Codiagonal: a loop whose body is itself a loop over the same variable is
    -- one loop.  `[ id , i₂ ]` is Bloom-Ésik's `∇` on the two copies of `A`.
    iter-cod : (w : S ⊗₀ A ⇒ S ⊗₀ ((B + A) + A))
             → iter (iter w) ≈ iter (id ⊗₁ [ id , i₂ ] ∘ w)
