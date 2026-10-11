{-# OPTIONS --safe --without-K #-}

-- Simulation along a relation.  A relation between two machines' states — and
-- between their interfaces — is a span: an apex machine whose states are the
-- related pairs, simulated into each machine (`RelSim`).  The apex's point is a
-- COUPLING of the two points (each leg carries it to one of them) and its step
-- a coupling of the two steps, so outputs are related exactly when the output
-- legs agree on them.  The legs are simulations along pure interface maps
-- (`_≲[_∣_]_`), of which `_≲_` is the identity case; they compose under
-- `_∘ᴹ_`, `_⊗ᵉ_` and `traceᴹ` — the last by `iter-transfer`, which moves the
-- loop variable along with the state — so a relational simulation of a circuit
-- is assembled from its leaves.  With identity legs outside, the apex simulates
-- both machines, which are then `_≈ᴹ_` (`relsim⇒≈ᴹ`); `_≲_` is the graph case
-- (`≲⇒relsim`).

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Function.Bundles using (_⇔_; mk⇔)
open import Level

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Iteration as Iteration
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Trace as Trace

module CategoricalCrypto.Machines.Sim.Relational
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱)
  (E : Iteration.Elgot 𝒱 dist 𝒫) where

open SymmetricMonoidalCategory 𝒱
open Core 𝒱
open Frame 𝒱
open Iteration.Elgot E
open MD.MonoidalDistributive dist
open MDP 𝒱 dist
open MonoidalUtilities.Shorthands monoidal
open PureSub 𝒫
open Sim 𝒱 𝒫
open Tensor 𝒱 dist 𝒫
open Trace 𝒱 dist 𝒫 E

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric
open import Categories.Morphism.Reasoning U

private variable
  A A′ A″ B B′ B″ C C′ D D′ P Q R X X′ Y Y′ Z : Obj
  Aᴿ Bᴿ Cᴿ Dᴿ Xᴿ : Obj

------------------------------------------------------------------------
-- Interface maps through the state actions

-- The interface-relabelling forms of `Frame.onL-sim`/`onR-sim` and
-- `Tensor.tstep-sim`: a state map on each factor and a map on each letter.
onL-sim[] : {v : P ⇒ R} {w : Q ⇒ Z} {μ : X ⇒ X′} {ν : Y ⇒ Y′}
            {k : P ⊗₀ X ⇒ P ⊗₀ Y} {k′ : R ⊗₀ X′ ⇒ R ⊗₀ Y′}
          → v ⊗₁ ν ∘ k ≈ k′ ∘ v ⊗₁ μ
          → (v ⊗₁ w) ⊗₁ ν ∘ onL k ≈ onL k′ ∘ (v ⊗₁ w) ⊗₁ μ
onL-sim[] {v = v} {w} {μ} {ν} e = begin
  (v ⊗₁ w) ⊗₁ ν ∘ (β ∘ (_ ⊗₁ id ∘ β))
    ≈⟨ pullˡ (β-nat v ν w) ○ assoc ⟩
  β ∘ ((v ⊗₁ ν) ⊗₁ w ∘ (_ ⊗₁ id ∘ β))
    ≈⟨ refl⟩∘⟨ pullˡ (parallel e id-comm) ⟩
  β ∘ ((_ ⊗₁ id ∘ (v ⊗₁ μ) ⊗₁ w) ∘ β)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  β ∘ (_ ⊗₁ id ∘ ((v ⊗₁ μ) ⊗₁ w ∘ β))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ β-nat v w μ ⟩
  β ∘ (_ ⊗₁ id ∘ (β ∘ (v ⊗₁ w) ⊗₁ μ))
    ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (β ∘ (_ ⊗₁ id ∘ β)) ∘ (v ⊗₁ w) ⊗₁ μ  ∎

onR-sim[] : {v : P ⇒ R} {w : Q ⇒ Z} {μ : X ⇒ X′} {ν : Y ⇒ Y′}
            {k : Q ⊗₀ X ⇒ Q ⊗₀ Y} {k′ : Z ⊗₀ X′ ⇒ Z ⊗₀ Y′}
          → w ⊗₁ ν ∘ k ≈ k′ ∘ w ⊗₁ μ
          → (v ⊗₁ w) ⊗₁ ν ∘ onR k ≈ onR k′ ∘ (v ⊗₁ w) ⊗₁ μ
onR-sim[] {v = v} {w} {μ} {ν} e = begin
  (v ⊗₁ w) ⊗₁ ν ∘ (α⇐ ∘ (id ⊗₁ _ ∘ α⇒))
    ≈⟨ pullˡ (⟺ assoc-commute-to) ○ assoc ⟩
  α⇐ ∘ (v ⊗₁ (w ⊗₁ ν) ∘ (id ⊗₁ _ ∘ α⇒))
    ≈⟨ refl⟩∘⟨ pullˡ (parallel id-comm e) ⟩
  α⇐ ∘ ((id ⊗₁ _ ∘ v ⊗₁ (w ⊗₁ μ)) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ (id ⊗₁ _ ∘ (v ⊗₁ (w ⊗₁ μ) ∘ α⇒))
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
  α⇐ ∘ (id ⊗₁ _ ∘ (α⇒ ∘ (v ⊗₁ w) ⊗₁ μ))
    ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (α⇐ ∘ (id ⊗₁ _ ∘ α⇒)) ∘ (v ⊗₁ w) ⊗₁ μ  ∎

-- A summandwise relabelling passes an injection as that summand's map.
relabel-i₁ : (v : P ⇒ R) (μ : A ⇒ A′) (ν : C ⇒ C′)
           → v ⊗₁ (μ +₁ ν) ∘ id ⊗₁ i₁ ≈ id ⊗₁ i₁ ∘ v ⊗₁ μ
relabel-i₁ _ _ _ = merge₂ʳ ○ (refl⟩⊗⟨ +₁∘i₁) ○ split₂ˡ

relabel-i₂ : (v : P ⇒ R) (μ : A ⇒ A′) (ν : C ⇒ C′)
           → v ⊗₁ (μ +₁ ν) ∘ id ⊗₁ i₂ ≈ id ⊗₁ i₂ ∘ v ⊗₁ ν
relabel-i₂ _ _ _ = merge₂ʳ ○ (refl⟩⊗⟨ +₁∘i₂) ○ split₂ˡ

-- `Iteration.tstep-pad` with a map on each summand.
tstep-relabel : (v : P ⇒ R) (μ : A ⇒ A′) (ν : C ⇒ C′)
              → tstep (v ⊗₁ μ) (v ⊗₁ ν) ≈ v ⊗₁ (μ +₁ ν)
tstep-relabel v μ ν = δ-unique (tstep-i₁ ○ ⟺ (relabel-i₁ v μ ν)) (tstep-i₂ ○ ⟺ (relabel-i₂ v μ ν))

tstep-sim[] : {v : X ⇒ X′} {μ₁ : A ⇒ A′} {ν₁ : B ⇒ B′} {μ₂ : C ⇒ C′} {ν₂ : D ⇒ D′}
              {k : X ⊗₀ A ⇒ X ⊗₀ B} {k′ : X′ ⊗₀ A′ ⇒ X′ ⊗₀ B′}
              {l : X ⊗₀ C ⇒ X ⊗₀ D} {l′ : X′ ⊗₀ C′ ⇒ X′ ⊗₀ D′}
            → v ⊗₁ ν₁ ∘ k ≈ k′ ∘ v ⊗₁ μ₁ → v ⊗₁ ν₂ ∘ l ≈ l′ ∘ v ⊗₁ μ₂
            → v ⊗₁ (ν₁ +₁ ν₂) ∘ tstep k l ≈ tstep k′ l′ ∘ v ⊗₁ (μ₁ +₁ μ₂)
tstep-sim[] {v = v} {μ₁} {ν₁} {μ₂} {ν₂} e₁ e₂ = δ-unique
  (pullʳ tstep-i₁ ○ pullˡ (relabel-i₁ v ν₁ ν₂) ○ assoc ○ (refl⟩∘⟨ e₁)
   ○ ⟺ (pullʳ (relabel-i₁ v μ₁ μ₂) ○ pullˡ tstep-i₁ ○ assoc))
  (pullʳ tstep-i₂ ○ pullˡ (relabel-i₂ v ν₁ ν₂) ○ assoc ○ (refl⟩∘⟨ e₂)
   ○ ⟺ (pullʳ (relabel-i₂ v μ₁ μ₂) ○ pullˡ tstep-i₂ ○ assoc))

-- `Trace.Congruence.traceStep-sim` with a map on each of the three interfaces:
-- `iter-transfer` moves the loop variable along `ξ` and the state along `θ`.
module _ (S T : State) (A B X A′ B′ X′ : Obj)
  {k : obj S ⊗₀ (A + X) ⇒ obj S ⊗₀ (B + X)} {k′ : obj T ⊗₀ (A′ + X′) ⇒ obj T ⊗₀ (B′ + X′)}
  {θ : obj S ⇒ obj T} {μ : A ⇒ A′} {ν : B ⇒ B′} {ξ : X ⇒ X′}
  (θᵖ : Pure θ) (νᵖ : Pure ν) (ξᵖ : Pure ξ)
  (θˢ : θ ⊗₁ (ν +₁ ξ) ∘ k ≈ k′ ∘ θ ⊗₁ (μ +₁ ξ)) where

  private
    loop-sim : loopBody T A′ B′ X′ k′ ∘ θ ⊗₁ ξ ≈ tstep (θ ⊗₁ ν) (θ ⊗₁ ξ) ∘ loopBody S A B X k
    loop-sim = assoc ○ (refl⟩∘⟨ ⟺ (relabel-i₂ θ μ ξ)) ○ sym-assoc ○ (⟺ θˢ ⟩∘⟨refl) ○ assoc
             ○ (⟺ (tstep-relabel θ ν ξ) ⟩∘⟨refl)

    loop-transfer : iter (loopBody T A′ B′ X′ k′) ∘ θ ⊗₁ ξ ≈ θ ⊗₁ ν ∘ iter (loopBody S A B X k)
    loop-transfer = iter-transfer (θ ⊗₁ ξ) (θ ⊗₁ ν) (pure-⊗₁ θᵖ ξᵖ) (pure-⊗₁ θᵖ νᵖ) loop-sim

  solve-sim[] : θ ⊗₁ ν ∘ solve S A B X k ≈ solve T A′ B′ X′ k′ ∘ θ ⊗₁ (ν +₁ ξ)
  solve-sim[] = δ-unique
    ((pullʳ (solve-i₁ S A B X k) ○ identityʳ)
     ○ ⟺ (pullʳ (relabel-i₁ θ ν ξ) ○ pullˡ (solve-i₁ T A′ B′ X′ k′) ○ identityˡ))
    (pullʳ (solve-i₂ S A B X k) ○ ⟺ loop-transfer
     ○ ⟺ (pullʳ (relabel-i₂ θ ν ξ) ○ pullˡ (solve-i₂ T A′ B′ X′ k′)))

  traceStep-sim[] : θ ⊗₁ ν ∘ traceStep S A B X k ≈ traceStep T A′ B′ X′ k′ ∘ θ ⊗₁ μ
  traceStep-sim[] = sym-assoc ○ (solve-sim[] ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ enter)
                  ○ (refl⟩∘⟨ sym-assoc) ○ sym-assoc
    where
      enter : θ ⊗₁ (ν +₁ ξ) ∘ (k ∘ id ⊗₁ i₁) ≈ k′ ∘ (id ⊗₁ i₁ ∘ θ ⊗₁ μ)
      enter = sym-assoc ○ (θˢ ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ relabel-i₁ θ μ ξ)

------------------------------------------------------------------------
-- Simulation along interface maps

infix 4 _≲[_∣_]_

-- The state map carries each step, relabelling its input by `μᵢ` and its
-- output by `μₒ`.
record _≲[_∣_]_ {A B A′ B′ : Obj} (f : Machine A B) (μᵢ : A ⇒ A′) (μₒ : B ⇒ B′)
                (g : Machine A′ B′) : Set (ℓ ⊔ e) where
  field
    leg       : St f ⇒ St g
    leg-pure  : Pure leg
    leg-point : leg ∘ point (state f) ≈ point (state g)
    leg-step  : leg ⊗₁ μₒ ∘ step f ≈ step g ∘ leg ⊗₁ μᵢ

open _≲[_∣_]_ public

≲⇒≲[id] : {f g : Machine A B} → f ≲ g → f ≲[ id ∣ id ] g
≲⇒≲[id] s = record { leg = θ s ; leg-pure = θ-pure s ; leg-point = θ-point s ; leg-step = θ-step s }

≲[id]⇒≲ : {f g : Machine A B} → f ≲[ id ∣ id ] g → f ≲ g
≲[id]⇒≲ s = record { θ = leg s ; θ-pure = leg-pure s ; θ-point = leg-point s ; θ-step = leg-step s }

≲⇔≲[id] : {f g : Machine A B} → f ≲ g ⇔ f ≲[ id ∣ id ] g
≲⇔≲[id] = mk⇔ ≲⇒≲[id] ≲[id]⇒≲

≲[]-resp-≈ : {f : Machine A B} {g : Machine A′ B′} {μ μ′ : A ⇒ A′} {ν ν′ : B ⇒ B′}
           → μ ≈ μ′ → ν ≈ ν′ → f ≲[ μ ∣ ν ] g → f ≲[ μ′ ∣ ν′ ] g
≲[]-resp-≈ eμ eν s = record
  { leg = leg s ; leg-pure = leg-pure s ; leg-point = leg-point s
  ; leg-step = ((refl⟩⊗⟨ ⟺ eν) ⟩∘⟨refl) ○ leg-step s ○ (refl⟩∘⟨ (refl⟩⊗⟨ eμ)) }

≲[]-trans : {f : Machine A B} {g : Machine A′ B′} {h : Machine A″ B″}
            {μ : A ⇒ A′} {ν : B ⇒ B′} {μ′ : A′ ⇒ A″} {ν′ : B′ ⇒ B″}
          → f ≲[ μ ∣ ν ] g → g ≲[ μ′ ∣ ν′ ] h → f ≲[ μ′ ∘ μ ∣ ν′ ∘ ν ] h
≲[]-trans s t = record
  { leg       = leg t ∘ leg s
  ; leg-pure  = pure-∘ (leg-pure t) (leg-pure s)
  ; leg-point = pullʳ (leg-point s) ○ leg-point t
  ; leg-step  = (⊗-distrib-over-∘ ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ leg-step s) ○ sym-assoc
              ○ (leg-step t ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ ⟺ ⊗-distrib-over-∘)
  }

idᴹ-≲[] : (μ : A ⇒ A′) → idᴹ ≲[ μ ∣ μ ] idᴹ
idᴹ-≲[] μ = record
  { leg = id ; leg-pure = pure-id ; leg-point = identityˡ ; leg-step = identityʳ ○ ⟺ identityˡ }

-- A pure machine is simulated along any square it commutes in.
pureᴹ-≲[] : {h : A ⇒ B} {h′ : A′ ⇒ B′} {μ : A ⇒ A′} {ν : B ⇒ B′}
          → ν ∘ h ≈ h′ ∘ μ → pureᴹ h ≲[ μ ∣ ν ] pureᴹ h′
pureᴹ-≲[] sq = record
  { leg = id ; leg-pure = pure-id ; leg-point = identityˡ
  ; leg-step = merge₂ˡ ○ (refl⟩⊗⟨ sq) ○ ⟺ merge₂ˡ }

opaque
  unfolding _∘ᴹ_

  ∘ᴹ-resp-≲[] : {f : Machine B C} {f′ : Machine B′ C′} {g : Machine A B} {g′ : Machine A′ B′}
                {μ : A ⇒ A′} {ν : B ⇒ B′} {ρ : C ⇒ C′}
              → f ≲[ ν ∣ ρ ] f′ → g ≲[ μ ∣ ν ] g′ → (f ∘ᴹ g) ≲[ μ ∣ ρ ] (f′ ∘ᴹ g′)
  ∘ᴹ-resp-≲[] {f = f} {f′} {g} {g′} u v = record
    { leg       = leg u ⊗₁ leg v
    ; leg-pure  = pure-⊗₁ (leg-pure u) (leg-pure v)
    ; leg-point = ⊛-point₂ (state f) (state f′) (state g) (state g′) (leg-point u) (leg-point v)
    ; leg-step  = pullˡ (onL-sim[] (leg-step u)) ○ assoc
                ○ (refl⟩∘⟨ onR-sim[] (leg-step v)) ○ sym-assoc
    }

⊗ᵉ-resp-≲[] : {f : Machine A B} {f′ : Machine A′ B′} {g : Machine C D} {g′ : Machine C′ D′}
              {μ₁ : A ⇒ A′} {ν₁ : B ⇒ B′} {μ₂ : C ⇒ C′} {ν₂ : D ⇒ D′}
            → f ≲[ μ₁ ∣ ν₁ ] f′ → g ≲[ μ₂ ∣ ν₂ ] g′
            → (f ⊗ᵉ g) ≲[ μ₁ +₁ μ₂ ∣ ν₁ +₁ ν₂ ] (f′ ⊗ᵉ g′)
⊗ᵉ-resp-≲[] {f = f} {f′} {g} {g′} u v = record
  { leg       = leg u ⊗₁ leg v
  ; leg-pure  = pure-⊗₁ (leg-pure u) (leg-pure v)
  ; leg-point = ⊛-point₂ (state f) (state f′) (state g) (state g′) (leg-point u) (leg-point v)
  ; leg-step  = tstep-sim[] (onL-sim[] (leg-step u)) (onR-sim[] (leg-step v))
  }

-- The loop's map `ξ` is on both sides of the body; output and loop maps must
-- be pure, for `iter-transfer`.
trace-resp-≲[] : {f : Machine (A + X) (B + X)} {g : Machine (A′ + X′) (B′ + X′)}
                 {μ : A ⇒ A′} {ν : B ⇒ B′} {ξ : X ⇒ X′}
               → Pure ν → Pure ξ → f ≲[ μ +₁ ξ ∣ ν +₁ ξ ] g
               → traceᴹ A B X f ≲[ μ ∣ ν ] traceᴹ A′ B′ X′ g
trace-resp-≲[] {A = A} {X = X} {B = B} {A′ = A′} {X′ = X′} {B′ = B′} {f = f} {g} νᵖ ξᵖ s = record
  { leg       = leg s
  ; leg-pure  = leg-pure s
  ; leg-point = leg-point s
  ; leg-step  = traceStep-sim[] (state f) (state g) A B X A′ B′ X′ (leg-pure s) νᵖ ξᵖ (leg-step s)
  }

------------------------------------------------------------------------
-- Relational simulation

-- `f` and `g` related along the interface spans `a₁ , a₂` and `b₁ , b₂`: an
-- apex simulated into both, whose state object is the relation on states.
record RelSim {A B A′ B′ Aᴿ Bᴿ : Obj} (a₁ : Aᴿ ⇒ A) (a₂ : Aᴿ ⇒ A′) (b₁ : Bᴿ ⇒ B) (b₂ : Bᴿ ⇒ B′)
              (f : Machine A B) (g : Machine A′ B′) : Set (o ⊔ ℓ ⊔ e) where
  field
    apex  : Machine Aᴿ Bᴿ
    left  : apex ≲[ a₁ ∣ b₁ ] f
    right : apex ≲[ a₂ ∣ b₂ ] g

open RelSim public

-- The graph of a state map: the apex is `f` itself.
≲⇒relsim : {f g : Machine A B} → f ≲ g → RelSim id id id id f g
≲⇒relsim s = record { apex = _ ; left = ≲⇒≲[id] ≲-refl ; right = ≲⇒≲[id] s }

relsim⇒≈ᴹ : {f g : Machine A B} → RelSim id id id id f g → f ≈ᴹ g
relsim⇒≈ᴹ r = ≲⇒≈ᴹ˘ (≲[id]⇒≲ (left r)) ○ᴹ ≲⇒≈ᴹ (≲[id]⇒≲ (right r))

∘ᴹ-relsim : {f : Machine B C} {f′ : Machine B′ C′} {g : Machine A B} {g′ : Machine A′ B′}
            {a₁ : Aᴿ ⇒ A} {a₂ : Aᴿ ⇒ A′} {b₁ : Bᴿ ⇒ B} {b₂ : Bᴿ ⇒ B′}
            {c₁ : Cᴿ ⇒ C} {c₂ : Cᴿ ⇒ C′}
          → RelSim b₁ b₂ c₁ c₂ f f′ → RelSim a₁ a₂ b₁ b₂ g g′
          → RelSim a₁ a₂ c₁ c₂ (f ∘ᴹ g) (f′ ∘ᴹ g′)
∘ᴹ-relsim r s = record
  { apex = apex r ∘ᴹ apex s
  ; left = ∘ᴹ-resp-≲[] (left r) (left s) ; right = ∘ᴹ-resp-≲[] (right r) (right s) }

⊗ᵉ-relsim : {f : Machine A B} {f′ : Machine A′ B′} {g : Machine C D} {g′ : Machine C′ D′}
            {a₁ : Aᴿ ⇒ A} {a₂ : Aᴿ ⇒ A′} {b₁ : Bᴿ ⇒ B} {b₂ : Bᴿ ⇒ B′}
            {c₁ : Cᴿ ⇒ C} {c₂ : Cᴿ ⇒ C′} {d₁ : Dᴿ ⇒ D} {d₂ : Dᴿ ⇒ D′}
          → RelSim a₁ a₂ b₁ b₂ f f′ → RelSim c₁ c₂ d₁ d₂ g g′
          → RelSim (a₁ +₁ c₁) (a₂ +₁ c₂) (b₁ +₁ d₁) (b₂ +₁ d₂) (f ⊗ᵉ g) (f′ ⊗ᵉ g′)
⊗ᵉ-relsim r s = record
  { apex = apex r ⊗ᵉ apex s
  ; left = ⊗ᵉ-resp-≲[] (left r) (left s) ; right = ⊗ᵉ-resp-≲[] (right r) (right s) }

-- The loop relation `x₁ , x₂` sits on both sides of the body.
trace-relsim : {f : Machine (A + X) (B + X)} {g : Machine (A′ + X′) (B′ + X′)}
               {a₁ : Aᴿ ⇒ A} {a₂ : Aᴿ ⇒ A′} {b₁ : Bᴿ ⇒ B} {b₂ : Bᴿ ⇒ B′}
               {x₁ : Xᴿ ⇒ X} {x₂ : Xᴿ ⇒ X′}
             → Pure b₁ → Pure b₂ → Pure x₁ → Pure x₂
             → RelSim (a₁ +₁ x₁) (a₂ +₁ x₂) (b₁ +₁ x₁) (b₂ +₁ x₂) f g
             → RelSim a₁ a₂ b₁ b₂ (traceᴹ A B X f) (traceᴹ A′ B′ X′ g)
trace-relsim {Aᴿ = Aᴿ} {Bᴿ = Bᴿ} {Xᴿ = Xᴿ} b₁ᵖ b₂ᵖ x₁ᵖ x₂ᵖ r = record
  { apex  = traceᴹ Aᴿ Bᴿ Xᴿ (apex r)
  ; left  = trace-resp-≲[] b₁ᵖ x₁ᵖ (left r)
  ; right = trace-resp-≲[] b₂ᵖ x₂ᵖ (right r) }
