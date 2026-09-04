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
-- Statement deviation, deliberate: `iter-uniform` is stated along an arbitrary
-- state map rather than along a state *iso*.  The iso form suffices for every
-- state reconciliation the trace laws below perform, but the simulation
-- equality's congruence for `traceᴹ` needs uniformity along the simulation's
-- own state map, which is not invertible.  At a Kleisli base neither form is
-- inhabited as literally stated — an arbitrary Kleisli map is effectful, and
-- iteration transfers along *pure* maps only — so the promotion restricts both
-- this field and `_≲_`'s state map to a wide subcategory of pure maps.  That
-- restriction is the fourth residual of `CategoricalCrypto.Machines.Trace`.

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
import Categories.Category.Monoidal.Distributive as MD
open import Level using (levelOfTerm)

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.Machines.Iteration
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱 using (onR)
open MD.MonoidalDistributive dist
open Tensor 𝒱 dist using (tstep)

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

    iter-uniform : (θ : S ⇒ T) {v : T ⊗₀ A ⇒ T ⊗₀ (B + A)}
                 → v ∘ pad θ ≈ pad θ ∘ u → iter v ∘ pad θ ≈ pad θ ∘ iter u

    -- Codiagonal: a loop whose body is itself a loop over the same variable is
    -- one loop.  `[ id , i₂ ]` is Bloom-Ésik's `∇` on the two copies of `A`.
    iter-cod : (w : S ⊗₀ A ⇒ S ⊗₀ ((B + A) + A))
             → iter (iter w) ≈ iter (id ⊗₁ [ id , i₂ ] ∘ w)
