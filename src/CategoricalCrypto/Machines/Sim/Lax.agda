{-# OPTIONS --safe --without-K #-}

-- Simulation up to an initialization prefix.
--
-- `Machines.Sim`'s generator equates the two points on the nose, which is too
-- strict for a machine that carries a dead-weight component: a scalar
-- `σ : unit ⇒ unit` buried in a composite contributes its own initialization to
-- the run and nothing else, and no state map can make that disappear.  `_≲ˡ[_]_`
-- records exactly that gap — step and state map as strict as `_≲_`, the point
-- only up to a scalar prefix — and the run-level payoff is that an almost surely
-- terminating prefix is invisible to an ε-closed comparison
-- (`Dp.Mass.astotal-bind`; the cash-out is `UC.Machine.Run.Lax`).
--
-- Two shapes are forced by that payoff.  There is no `θ-discard` field: the
-- discard of a state object is arbitrary data at a Kleisli base, so a scalar's
-- own discard is not pure and could not be the state map of a simulation into
-- the trivial state.  Nothing below or downstream spends it.  And the scalar is
-- an INDEX rather than a field, so that a congruence names the scalar it
-- produces (`σ ∘ τ` for a composite) and the consumer can normalize it with
-- `≲ˡ-resp-scalar` instead of re-deriving a mass bound.
--
-- The congruences are the strict ones with `Frame.⊛-point₂ˡ` — scalars are
-- central, so the two factors' prefixes merge — swapped in for `⊛-point₂`; the
-- trace's is free, since `traceᴹ` keeps its argument's state and only
-- `traceStep-sim` is about the step.  `_≈ˡ[_]_` closes the relation under the
-- category's own equality at both ends, which a bare `_≲ˡ[_]_` is not: a
-- backwards generator of `_≈ᴹ_` supplies no state map to compose with.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
import Categories.Category.Monoidal.Distributive as MD

open import Level

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Iteration as Iteration
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Congruence as TraceCong

module CategoricalCrypto.Machines.Sim.Lax
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱)
  (E : Iteration.Elgot 𝒱 dist 𝒫) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open Equiv
open Frame 𝒱
open MCat 𝒱 𝒫
open MD.MonoidalDistributive dist
open PureSub 𝒫
open Sim 𝒱 𝒫
open Tensor 𝒱 dist 𝒫
open Trace 𝒱 dist 𝒫 E
open TraceCong 𝒱 dist 𝒫 E

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable
  A B C D X : Obj
  σ τ : unit ⇒ unit

infix 4 _≲ˡ[_]_ _≈ˡ[_]_

record _≲ˡ[_]_ {A B : Obj} (f : Machine A B) (σ : unit ⇒ unit) (g : Machine A B)
       : Set (ℓ ⊔ e) where
  field
    θˡ       : St f ⇒ St g
    θˡ-pure  : Pure θˡ
    θˡ-point : θˡ ∘ point (state f) ≈ point (state g) ∘ σ
    θˡ-step  : θˡ ⊗₁ id ∘ step f ≈ step g ∘ θˡ ⊗₁ id

open _≲ˡ[_]_ public

≲ˡ-resp-scalar : {f g : Machine A B} → σ ≈ τ → f ≲ˡ[ σ ] g → f ≲ˡ[ τ ] g
≲ˡ-resp-scalar eq l = record
  { θˡ = θˡ l ; θˡ-pure = θˡ-pure l
  ; θˡ-point = θˡ-point l ○ (refl⟩∘⟨ eq) ; θˡ-step = θˡ-step l }

≲⇒≲ˡ : {f g : Machine A B} → f ≲ g → f ≲ˡ[ id ] g
≲⇒≲ˡ s = record
  { θˡ = θ s ; θˡ-pure = θ-pure s
  ; θˡ-point = θ-point s ○ ⟺ identityʳ ; θˡ-step = θ-step s }

≲ˡ-refl : {f : Machine A B} → f ≲ˡ[ id ] f
≲ˡ-refl = ≲⇒≲ˡ ≲-refl

≲ˡ-trans : {f g h : Machine A B} → f ≲ˡ[ σ ] g → g ≲ˡ[ τ ] h → f ≲ˡ[ τ ∘ σ ] h
≲ˡ-trans s t = record
  { θˡ       = θˡ t ∘ θˡ s
  ; θˡ-pure  = pure-∘ (θˡ-pure t) (θˡ-pure s)
  ; θˡ-point = pullʳ (θˡ-point s) ○ pullˡ (θˡ-point t) ○ assoc
  ; θˡ-step  = (split₁ˡ ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ θˡ-step s) ○ sym-assoc
             ○ (θˡ-step t ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ ⟺ split₁ˡ)
  }

------------------------------------------------------------------------
-- The congruences

opaque
  unfolding _∘ᴹ_

  ∘ᴹ-resp-≲ˡ : {f h : Machine B C} {g i : Machine A B}
             → f ≲ˡ[ σ ] h → g ≲ˡ[ τ ] i → (f ∘ᴹ g) ≲ˡ[ σ ∘ τ ] (h ∘ᴹ i)
  ∘ᴹ-resp-≲ˡ {f = f} {h} {g} {i} u v = record
    { θˡ       = θˡ u ⊗₁ θˡ v
    ; θˡ-pure  = pure-⊗₁ (θˡ-pure u) (θˡ-pure v)
    ; θˡ-point = ⊛-point₂ˡ (state f) (state h) (state g) (state i)
                           (θˡ-point u) (θˡ-point v)
    ; θˡ-step  = pullˡ (onL-sim (θˡ-step u)) ○ assoc
               ○ (refl⟩∘⟨ onR-sim (θˡ-step v)) ○ sym-assoc
    }

⊗ᵉ-resp-≲ˡ : {f h : Machine A B} {g i : Machine C D}
           → f ≲ˡ[ σ ] h → g ≲ˡ[ τ ] i → (f ⊗ᵉ g) ≲ˡ[ σ ∘ τ ] (h ⊗ᵉ i)
⊗ᵉ-resp-≲ˡ {f = f} {h} {g} {i} u v = record
  { θˡ       = θˡ u ⊗₁ θˡ v
  ; θˡ-pure  = pure-⊗₁ (θˡ-pure u) (θˡ-pure v)
  ; θˡ-point = ⊛-point₂ˡ (state f) (state h) (state g) (state i)
                         (θˡ-point u) (θˡ-point v)
  ; θˡ-step  = tstep-sim (onL-sim (θˡ-step u)) (onR-sim (θˡ-step v))
  }

trace-resp-≲ˡ : {f g : Machine (A + X) (B + X)}
              → f ≲ˡ[ σ ] g → traceᴹ A B X f ≲ˡ[ σ ] traceᴹ A B X g
trace-resp-≲ˡ {A = A} {X = X} {B = B} {f = f} {g = g} l = record
  { θˡ       = θˡ l
  ; θˡ-pure  = θˡ-pure l
  ; θˡ-point = θˡ-point l
  ; θˡ-step  = traceStep-sim (state f) (state g) A B X (θˡ l) (θˡ-pure l) (θˡ-step l)
  }

------------------------------------------------------------------------
-- Closed under the category's own equality

record _≈ˡ[_]_ {A B : Obj} (f : Machine A B) (σ : unit ⇒ unit) (g : Machine A B)
       : Set (o ⊔ ℓ ⊔ e) where
  field
    {srcˡ tgtˡ} : Machine A B
    fromˡ : f ≈ᴹ srcˡ
    coreˡ : srcˡ ≲ˡ[ σ ] tgtˡ
    toˡ   : tgtˡ ≈ᴹ g

open _≈ˡ[_]_ public

≲ˡ⇒≈ˡ : {f g : Machine A B} → f ≲ˡ[ σ ] g → f ≈ˡ[ σ ] g
≲ˡ⇒≈ˡ l = record { fromˡ = reflᴹ ; coreˡ = l ; toˡ = reflᴹ }

≈ᴹ⇒≈ˡ : {f g : Machine A B} → f ≈ᴹ g → f ≈ˡ[ id ] g
≈ᴹ⇒≈ˡ eq = record { fromˡ = eq ; coreˡ = ≲ˡ-refl ; toˡ = reflᴹ }

≈ˡ-refl : {f : Machine A B} → f ≈ˡ[ id ] f
≈ˡ-refl = ≲ˡ⇒≈ˡ ≲ˡ-refl

≈ˡ-congˡ : {f f′ g : Machine A B} → f ≈ᴹ f′ → f′ ≈ˡ[ σ ] g → f ≈ˡ[ σ ] g
≈ˡ-congˡ eq l = record { fromˡ = eq ○ᴹ fromˡ l ; coreˡ = coreˡ l ; toˡ = toˡ l }

≈ˡ-congʳ : {f g g′ : Machine A B} → f ≈ˡ[ σ ] g → g ≈ᴹ g′ → f ≈ˡ[ σ ] g′
≈ˡ-congʳ l eq = record { fromˡ = fromˡ l ; coreˡ = coreˡ l ; toˡ = toˡ l ○ᴹ eq }

≈ˡ-resp-scalar : {f g : Machine A B} → σ ≈ τ → f ≈ˡ[ σ ] g → f ≈ˡ[ τ ] g
≈ˡ-resp-scalar eq l = record
  { fromˡ = fromˡ l ; coreˡ = ≲ˡ-resp-scalar eq (coreˡ l) ; toˡ = toˡ l }

∘ᴹ-resp-≈ˡ : {f h : Machine B C} {g i : Machine A B}
           → f ≈ˡ[ σ ] h → g ≈ˡ[ τ ] i → (f ∘ᴹ g) ≈ˡ[ σ ∘ τ ] (h ∘ᴹ i)
∘ᴹ-resp-≈ˡ u v = record
  { fromˡ = ∘ᴹ-resp-≈ᴹ (fromˡ u) (fromˡ v)
  ; coreˡ = ∘ᴹ-resp-≲ˡ (coreˡ u) (coreˡ v)
  ; toˡ   = ∘ᴹ-resp-≈ᴹ (toˡ u) (toˡ v) }

⊗ᵉ-resp-≈ˡ : {f h : Machine A B} {g i : Machine C D}
           → f ≈ˡ[ σ ] h → g ≈ˡ[ τ ] i → (f ⊗ᵉ g) ≈ˡ[ σ ∘ τ ] (h ⊗ᵉ i)
⊗ᵉ-resp-≈ˡ u v = record
  { fromˡ = ⊗ᵉ-resp-≈ᴹ (fromˡ u) (fromˡ v)
  ; coreˡ = ⊗ᵉ-resp-≲ˡ (coreˡ u) (coreˡ v)
  ; toˡ   = ⊗ᵉ-resp-≈ᴹ (toˡ u) (toˡ v) }

trace-resp-≈ˡ : {f g : Machine (A + X) (B + X)}
              → f ≈ˡ[ σ ] g → traceᴹ A B X f ≈ˡ[ σ ] traceᴹ A B X g
trace-resp-≈ˡ l = record
  { fromˡ = trace-resp-≈ᴹ (fromˡ l)
  ; coreˡ = trace-resp-≲ˡ (coreˡ l)
  ; toˡ   = trace-resp-≈ᴹ (toˡ l) }
