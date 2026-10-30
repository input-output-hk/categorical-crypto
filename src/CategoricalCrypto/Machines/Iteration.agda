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
-- Uniformity is asked in TRANSFER form, along a pure reindexing of the state
-- *and* the loop variable: `vanishing₂` and `trace-comm` move the loop
-- variable, which no state-only uniformity can do, and an effectful reindexing
-- replayed on both sides of a loop would duplicate its effect (which is why
-- `_≲_`'s state map is drawn from the same class `𝒫`).  The state-only form
-- (`iter-uniform`) is derived below.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP

open import Level

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.Machines.Iteration
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open Equiv
open Frame 𝒱
open MD.MonoidalDistributive dist
open MDP 𝒱 dist
open PureSub 𝒫
open Tensor 𝒱 dist 𝒫

open import Categories.Category.Monoidal.Reasoning monoidal

private variable A B C P S T : Obj
private variable u v : S ⊗₀ A ⇒ S ⊗₀ (B + A)

record Elgot : Set (levelOfTerm 𝒱) where
  field
    iter : (S ⊗₀ A ⇒ S ⊗₀ (B + A)) → S ⊗₀ A ⇒ S ⊗₀ B

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

    -- The transfers `vanishing₂` and `trace-comm` take reindex the LOOP
    -- VARIABLE by the coproduct structure, so `𝒫` has to contain it.  These
    -- cannot be fields of `PureSub`, which is stated over `𝒱` alone.
    pure-i₁ : Pure (i₁ {A} {B})
    pure-i₂ : Pure (i₂ {A} {B})
    pure-[] : {f : A ⇒ C} {g : B ⇒ C} → Pure f → Pure g → Pure [ f , g ]

  -- `iter-transfer` along the identity.
  iter-cong : u ≈ v → iter u ≈ iter v
  iter-cong {u = u} {v} e =
    ⟺ (⟺ identityʳ ○ iter-transfer id id pure-id pure-id {u} {v} hyp ○ identityˡ)
    where
    hyp = identityʳ ○ ⟺ e ○ ⟺ ((tstep-id ⟩∘⟨refl) ○ identityˡ)

  pure-+₁ : {f : A ⇒ B} {g : C ⇒ P} → Pure f → Pure g → Pure (f +₁ g)
  pure-+₁ pf pg = pure-resp-≈ (+-unique +₁∘i₁ +₁∘i₂)
                              (pure-[] (pure-∘ pure-i₁ pf) (pure-∘ pure-i₂ pg))

  iter-uniform : {S T A B : Obj} {u : S ⊗₀ A ⇒ S ⊗₀ (B + A)} (θ : S ⇒ T) → Pure θ
               → {v : T ⊗₀ A ⇒ T ⊗₀ (B + A)}
               → v ∘ θ ⊗₁ id ≈ θ ⊗₁ id ∘ u → iter v ∘ θ ⊗₁ id ≈ θ ⊗₁ id ∘ iter u
  iter-uniform {A = A} {B} {u} θ θᵖ {v} hyp =
    iter-transfer (θ ⊗₁ id) (θ ⊗₁ id)
                  (pure-⊗₁ θᵖ pure-id) (pure-⊗₁ θᵖ pure-id)
                  (hyp ○ (⟺ (tstep-pad θ) ⟩∘⟨refl))
