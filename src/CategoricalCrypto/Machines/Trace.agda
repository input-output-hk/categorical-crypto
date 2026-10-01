{-# OPTIONS --safe --without-K #-}

-- The ⊕-trace on the machine layer, built from the base's iteration.
--
-- One external step of `traceᴹ` feeds its input in on the `A` summand, then
-- solves the loop: `δ⇐` splits the emitted letter, an external `B` exits and a
-- loop `X` re-enters the body under `iter`.
--
-- The three interface objects of `traceᴹ` are explicit because `_+_` is a
-- coproduct *projection*, not a constructor, so Agda cannot recover `X` from
-- the type of a machine `Machine (A + X) (B + X)`.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Iteration as Iteration
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.Machines.Trace
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱)
  (E : Iteration.Elgot 𝒱 dist 𝒫) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided
open Core 𝒱
open Equiv
open Frame 𝒱
open Iteration 𝒱 dist 𝒫
open Iteration.Elgot E
open MD.MonoidalDistributive dist
open MDP 𝒱 dist
open PureSub 𝒫
open Sim 𝒱 𝒫
open Tensor 𝒱 dist 𝒫

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B C P Q X : Obj

------------------------------------------------------------------------
-- Solving the loop

module _ (S : State) (A B X : Obj) (k : obj S ⊗₀ (A + X) ⇒ obj S ⊗₀ (B + X)) where

  -- One pass of the loop: re-enter the body on the `X` summand.
  loopBody : obj S ⊗₀ X ⇒ obj S ⊗₀ (B + X)
  loopBody = k ∘ id ⊗₁ i₂

  -- Exit on `B`, iterate on `X`.
  solve : obj S ⊗₀ (B + X) ⇒ obj S ⊗₀ B
  solve = [ id , iter loopBody ] ∘ δ⇐

  traceStep : obj S ⊗₀ A ⇒ obj S ⊗₀ B
  traceStep = solve ∘ k ∘ id ⊗₁ i₁

  solve-i₁ : solve ∘ id ⊗₁ i₁ ≈ id
  solve-i₁ = pullʳ δ⇐-i₁ ○ inject₁

  solve-i₂ : solve ∘ id ⊗₁ i₂ ≈ iter loopBody
  solve-i₂ = pullʳ δ⇐-i₂ ○ inject₂

  -- The fixpoint law, in the form the trace laws consume it.
  solve-loop : iter loopBody ≈ solve ∘ loopBody
  solve-loop = iter-fix ○ sym-assoc

traceᴹ : (A B X : Obj) → Machine (A + X) (B + X) → Machine A B
traceᴹ A B X f = mk (state f) (traceStep (state f) A B X (step f))

traceStep-cong : (S : State) (A B X : Obj)
                 {k k′ : obj S ⊗₀ (A + X) ⇒ obj S ⊗₀ (B + X)}
               → k ≈ k′ → traceStep S A B X k ≈ traceStep S A B X k′
traceStep-cong S A B X e =
  ([]-cong₂ refl (iter-cong (e ⟩∘⟨refl)) ⟩∘⟨refl) ⟩∘⟨ (e ⟩∘⟨refl)

traceᴹ-cong : (S : State) (A B X : Obj)
              {k k′ : obj S ⊗₀ (A + X) ⇒ obj S ⊗₀ (B + X)}
            → k ≈ k′ → traceᴹ A B X (mk S k) ≲ traceᴹ A B X (mk S k′)
traceᴹ-cong S A B X e = mk-cong (traceStep-cong S A B X e)

------------------------------------------------------------------------
-- Yanking

-- The braiding's loop body exits on its first pass, so `iter` collapses after
-- one unfolding.
private
  iter-σᴹ : {X : Obj} → iter (loopBody Iˢ X X X (step (σᴹ {X} {X}))) ≈ id
  iter-σᴹ = iter-fix ○ (refl⟩∘⟨ refl⟩∘⟨ (merge₂ʳ ○ refl⟩⊗⟨ inject₂))
          ○ (refl⟩∘⟨ δ⇐-i₁) ○ inject₁

  yank-step : {X : Obj} → traceStep Iˢ X X X (step (σᴹ {X} {X})) ≈ id
  yank-step {X} = (refl⟩∘⟨ (merge₂ʳ ○ refl⟩⊗⟨ inject₁)) ○ solve-i₂ Iˢ X X X _ ○ iter-σᴹ

yankingᴹ : {X : Obj} → traceᴹ X X X (σᴹ {X} {X}) ≲ idᴹ
yankingᴹ = mk-cong yank-step

------------------------------------------------------------------------
-- Vanishing on the unit

-- `f ⊗ᵉ idᴹ` answers an `i₁` input on `i₁`, so the loop branch is never
-- entered: `tstep-i₁` routes the input straight past `solve`.
private
  van₁-step : {A B : Obj} (f : Machine A B)
            → traceStep (state (f ⊗ᵉ idᴹ {⊥})) A B ⊥ (step (f ⊗ᵉ idᴹ {⊥}))
            ≈ onL (step f)
  van₁-step {A = A} {B} f =
      (refl⟩∘⟨ tstep-i₁) ○ sym-assoc
    ○ (solve-i₁ (state (f ⊗ᵉ idᴹ {⊥})) A B ⊥ _ ⟩∘⟨refl) ○ identityˡ

vanishing₁ᴹ : {A B : Obj} (f : Machine A B) → traceᴹ A B ⊥ (f ⊗ᵉ idᴹ {⊥}) ≲ f
vanishing₁ᴹ f = ≲-trans (mk-cong (van₁-step f)) (collapseʳ onL-collapseʳ)

------------------------------------------------------------------------
-- Naturality at the step level

-- Right naturality is ⊕-side only: `tstep n id` leaves the loop branch alone,
-- so the loop — and with it `iter` — is untouched.
traceStep-∘ʳ : (S : State) (A B C X : Obj)
               (k : obj S ⊗₀ (A + X) ⇒ obj S ⊗₀ (B + X))
               (n : obj S ⊗₀ C ⇒ obj S ⊗₀ A)
             → traceStep S A B X k ∘ n ≈ traceStep S C B X (k ∘ tstep n id)
traceStep-∘ʳ S A B C X k n = assoc ○ ⟺ (sv ⟩∘⟨ ent)
  where
    lb : loopBody S C B X (k ∘ tstep n id) ≈ loopBody S A B X k
    lb = assoc ○ (refl⟩∘⟨ (tstep-i₂ ○ identityʳ))

    sv : solve S C B X (k ∘ tstep n id) ≈ solve S A B X k
    sv = []-cong₂ refl (iter-cong lb) ⟩∘⟨refl

    ent : (k ∘ tstep n id) ∘ id ⊗₁ i₁ ≈ (k ∘ id ⊗₁ i₁) ∘ n
    ent = assoc ○ (refl⟩∘⟨ tstep-i₁) ○ sym-assoc

-- Left naturality is where `iter-out` is spent: post-composing the exit branch
-- of the dispatch is the same as post-composing the whole loop.
solve-∘ˡ : (S : State) (A B C X : Obj)
           (k : obj S ⊗₀ (A + X) ⇒ obj S ⊗₀ (B + X)) (m : obj S ⊗₀ B ⇒ obj S ⊗₀ C)
         → solve S A C X (tstep m id ∘ k) ∘ tstep m id ≈ m ∘ solve S A B X k
solve-∘ˡ S A B C X k m = δ-unique branch₁ branch₂
  where
    branch₁ = (assoc ○ (refl⟩∘⟨ tstep-i₁) ○ sym-assoc
               ○ (solve-i₁ S A C X (tstep m id ∘ k) ⟩∘⟨refl) ○ identityˡ)
            ○ ⟺ (assoc ○ (refl⟩∘⟨ solve-i₁ S A B X k) ○ identityʳ)

    branch₂ = (assoc ○ (refl⟩∘⟨ (tstep-i₂ ○ identityʳ))
               ○ solve-i₂ S A C X (tstep m id ∘ k)
               ○ iter-cong assoc ○ ⟺ (iter-out m))
            ○ ⟺ (assoc ○ (refl⟩∘⟨ solve-i₂ S A B X k))

traceStep-∘ˡ : (S : State) (A B C X : Obj)
               (k : obj S ⊗₀ (A + X) ⇒ obj S ⊗₀ (B + X)) (m : obj S ⊗₀ B ⇒ obj S ⊗₀ C)
             → m ∘ traceStep S A B X k ≈ traceStep S A C X (tstep m id ∘ k)
traceStep-∘ˡ S A B C X k m =
    sym-assoc ○ (⟺ (solve-∘ˡ S A B C X k m) ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ sym-assoc)

------------------------------------------------------------------------
-- Extending the state

-- `onR` is functorial in the interface, which is all that is needed to slide it
-- past the dispatch; `iter-ctx` slides it past the loop.  The `onL` mirror is
-- `Trace.Congruence.traceStep-onL`, by conjugation with the braiding.
onR-pre : {Y Z W : Obj} {w : Q ⊗₀ Y ⇒ Q ⊗₀ Z} (j : W ⇒ Y)
        → onR {P = P} w ∘ id ⊗₁ j ≈ onR (w ∘ id ⊗₁ j)
onR-pre j = (refl⟩∘⟨ ⟺ (onR-id⊗ j)) ○ ⟺ onR-∘

module _ (P S : State) (A B X : Obj) (k : obj S ⊗₀ (A + X) ⇒ obj S ⊗₀ (B + X)) where

  solve-onR : solve (P ⊛ S) A B X (onR k) ≈ onR (solve S A B X k)
  solve-onR = δ-unique
    (solve-i₁ (P ⊛ S) A B X (onR k)
       ○ ⟺ (onR-pre i₁ ○ onR-cong (solve-i₁ S A B X k) ○ onR-id))
    (solve-i₂ (P ⊛ S) A B X (onR k) ○ iter-cong (onR-pre i₂) ○ iter-ctx
       ○ ⟺ (onR-pre i₂ ○ onR-cong (solve-i₂ S A B X k)))

  traceStep-onR : traceStep (P ⊛ S) A B X (onR k) ≈ onR (traceStep S A B X k)
  traceStep-onR = (solve-onR ⟩∘⟨ onR-pre i₁) ○ ⟺ onR-∘
