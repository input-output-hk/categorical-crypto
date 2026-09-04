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
-- Uniformity is asked in TRANSFER form: along a pure reindexing of the state
-- *and* the loop variable, with the output relabelled.  Three reasons.  It is
-- what the intended instance proves directly (its state-only corollary is
-- derived from it, not the other way round).  It is uninhabited outside `𝒫`,
-- since an effectful reindexing replayed on both sides of a loop would
-- duplicate its effect — which is also why `_≲_`'s state map is drawn from the
-- same class, so that the trace congruence lines up.  And the loop-variable
-- half is what `vanishing₂` and `trace-comm` run on: relating a loop over
-- `X + P` to nested loops over `X` and `P` moves the loop variable, and no
-- state-only uniformity can do that.  The classical state-only form
-- (`iter-uniform`) is derived below.

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Pure using (PureSub)
import Categories.Category.Monoidal.Distributive as MD
open import Level using (levelOfTerm)

import Categories.Category.Monoidal.Distributive.Properties as MDP

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.Machines.Iteration
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱 using (onR)
open Equiv
open Frame 𝒱 using (pad-transport)
open MD.MonoidalDistributive dist
open MDP 𝒱 dist using (δ-unique)
open PureSub 𝒫
open Tensor 𝒱 dist 𝒫 using (tstep; tstep-i₁; tstep-i₂)

open import Categories.Category.Monoidal.Reasoning monoidal

private variable A B C P S T : Obj
private variable u v : S ⊗₀ A ⇒ S ⊗₀ (B + A)

-- A state map padded out to a machine interface: the shape every state
-- reconciliation in the layer takes.
pad : S ⇒ T → S ⊗₀ A ⇒ T ⊗₀ A
pad θ = θ ⊗₁ id

-- A padded state map relabels a sum interface summandwise, hence is its own
-- `tstep`: the distributor is natural in the state.
tstep-pad : {S T X Y : Obj} (θ : S ⇒ T)
          → tstep (θ ⊗₁ id {X}) (θ ⊗₁ id {Y}) ≈ θ ⊗₁ id {X + Y}
tstep-pad θ = δ-unique (tstep-i₁ ○ pad-transport θ i₁) (tstep-i₂ ○ pad-transport θ i₂)

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

    iter-transfer : {S T A A′ B B′ : Obj}
                    (κ : S ⊗₀ A ⇒ T ⊗₀ A′) (μ : S ⊗₀ B ⇒ T ⊗₀ B′) → Pure κ → Pure μ
                  → {u : S ⊗₀ A ⇒ S ⊗₀ (B + A)} {v : T ⊗₀ A′ ⇒ T ⊗₀ (B′ + A′)}
                  → v ∘ κ ≈ tstep μ κ ∘ u → iter v ∘ κ ≈ μ ∘ iter u

    -- Codiagonal: a loop whose body is itself a loop over the same variable is
    -- one loop.  `[ id , i₂ ]` is Bloom-Ésik's `∇` on the two copies of `A`.
    iter-cod : (w : S ⊗₀ A ⇒ S ⊗₀ ((B + A) + A))
             → iter (iter w) ≈ iter (id ⊗₁ [ id , i₂ ] ∘ w)

  iter-uniform : {S T A B : Obj} {u : S ⊗₀ A ⇒ S ⊗₀ (B + A)} (θ : S ⇒ T) → Pure θ
               → {v : T ⊗₀ A ⇒ T ⊗₀ (B + A)}
               → v ∘ pad θ ≈ pad θ ∘ u → iter v ∘ pad θ ≈ pad θ ∘ iter u
  iter-uniform {A = A} {B} {u} θ θᵖ {v} hyp =
    iter-transfer (θ ⊗₁ id {A}) (θ ⊗₁ id {B})
                  (pure-⊗₁ θᵖ pure-id) (pure-⊗₁ θᵖ pure-id) {u} {v} tr
    where
      tr : v ∘ pad θ ≈ tstep (θ ⊗₁ id {B}) (θ ⊗₁ id {A}) ∘ u
      tr = hyp ○ (⟺ (tstep-pad θ) ⟩∘⟨refl)
