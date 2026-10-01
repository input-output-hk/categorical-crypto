{-# OPTIONS --safe --without-K #-}

-- Simulation up to an initialization prefix.
--
-- `Machines.Sim`'s generator equates the two points on the nose, which is too
-- strict for a machine that carries a dead-weight component: a scalar
-- `σ : unit ⇒ unit` buried in a composite contributes its own initialization to
-- the run and nothing else, and no state map makes that disappear.  `_≲ˡ[_]_`
-- records exactly that gap — step and state map as strict as `_≲_`, the point
-- only up to a scalar prefix; its run-level reading is `UC.Machine.Run.Lax`.
--
-- The scalar is an INDEX rather than a field, so that a congruence names the
-- scalar it produces (`σ ∘ τ` for a composite) and a consumer normalizes it
-- with `≲ˡ-resp-scalar` instead of re-deriving a mass bound.  `_≈ˡ[_]_` closes
-- the relation under the category's own equality at both ends, which a bare
-- `_≲ˡ[_]_` is not: a backwards generator of `_≈ᴹ_` supplies no state map to
-- compose with.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
import Categories.Category.Monoidal.Distributive as MD

open import Data.Product.Base using (_,_)
open import Level
open import Relation.Binary.Construct.Composition using (_;_)

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
  ; θˡ-step  = traceStep-sim (state f) (state g) A B X
                             (θˡ l) (θˡ-pure l) (θˡ-step l)
  }

------------------------------------------------------------------------
-- Closed under the category's own equality

-- `_;_` is stdlib's relational composition (U+037E, not a semicolon).
_≈ˡ[_]_ : {A B : Obj} → Machine A B → unit ⇒ unit → Machine A B → Set (o ⊔ ℓ ⊔ e)
f ≈ˡ[ σ ] g = (_≈ᴹ_ ; (_≲ˡ[ σ ]_ ; _≈ᴹ_)) f g

≲ˡ⇒≈ˡ : {f g : Machine A B} → f ≲ˡ[ σ ] g → f ≈ˡ[ σ ] g
≲ˡ⇒≈ˡ l = _ , reflᴹ , _ , l , reflᴹ

≈ᴹ⇒≈ˡ : {f g : Machine A B} → f ≈ᴹ g → f ≈ˡ[ id ] g
≈ᴹ⇒≈ˡ eq = _ , eq , _ , ≲ˡ-refl , reflᴹ

≈ˡ-refl : {f : Machine A B} → f ≈ˡ[ id ] f
≈ˡ-refl = ≲ˡ⇒≈ˡ ≲ˡ-refl

≈ˡ-congˡ : {f f′ g : Machine A B} → f ≈ᴹ f′ → f′ ≈ˡ[ σ ] g → f ≈ˡ[ σ ] g
≈ˡ-congˡ eq (_ , e , _ , l , e′) = _ , eq ○ᴹ e , _ , l , e′

≈ˡ-congʳ : {f g g′ : Machine A B} → f ≈ˡ[ σ ] g → g ≈ᴹ g′ → f ≈ˡ[ σ ] g′
≈ˡ-congʳ (_ , e , _ , l , e′) eq = _ , e , _ , l , e′ ○ᴹ eq

≈ˡ-resp-scalar : {f g : Machine A B} → σ ≈ τ → f ≈ˡ[ σ ] g → f ≈ˡ[ τ ] g
≈ˡ-resp-scalar eq (_ , e , _ , l , e′) = _ , e , _ , ≲ˡ-resp-scalar eq l , e′

∘ᴹ-resp-≈ˡ : {f h : Machine B C} {g i : Machine A B}
           → f ≈ˡ[ σ ] h → g ≈ˡ[ τ ] i → (f ∘ᴹ g) ≈ˡ[ σ ∘ τ ] (h ∘ᴹ i)
∘ᴹ-resp-≈ˡ (_ , e₁ , _ , l₁ , e₁′) (_ , e₂ , _ , l₂ , e₂′) =
  _ , ∘ᴹ-resp-≈ᴹ e₁ e₂ , _ , ∘ᴹ-resp-≲ˡ l₁ l₂ , ∘ᴹ-resp-≈ᴹ e₁′ e₂′

⊗ᵉ-resp-≈ˡ : {f h : Machine A B} {g i : Machine C D}
           → f ≈ˡ[ σ ] h → g ≈ˡ[ τ ] i → (f ⊗ᵉ g) ≈ˡ[ σ ∘ τ ] (h ⊗ᵉ i)
⊗ᵉ-resp-≈ˡ (_ , e₁ , _ , l₁ , e₁′) (_ , e₂ , _ , l₂ , e₂′) =
  _ , ⊗ᵉ-resp-≈ᴹ e₁ e₂ , _ , ⊗ᵉ-resp-≲ˡ l₁ l₂ , ⊗ᵉ-resp-≈ᴹ e₁′ e₂′

trace-resp-≈ˡ : {f g : Machine (A + X) (B + X)}
              → f ≈ˡ[ σ ] g → traceᴹ A B X f ≈ˡ[ σ ] traceᴹ A B X g
trace-resp-≈ˡ (_ , e , _ , l , e′) = _ , trace-resp-≈ᴹ e , _ , trace-resp-≲ˡ l , trace-resp-≈ᴹ e′
