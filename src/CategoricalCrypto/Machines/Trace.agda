{-# OPTIONS --safe --without-K #-}

-- The ⊕-trace on the machine layer, built from the base's iteration.
--
-- One external step of `traceᴹ` feeds its input in on the `A` summand, then
-- *solves* the loop: `δ⇐` splits the emitted letter, an external `B` exits and
-- a loop `X` re-enters the body, which is `iter`'s job.  `solve` is that
-- dispatch, and `solve-i₁`/`solve-i₂`/`solve-loop` are the whole interface to
-- `iter`.  The traced machine keeps its argument's state: the loop is solved
-- within one step, which is why an iteration-induced trace *yanks* where the
-- delayed feedback of a plain feedback category does not.
--
-- The three interface objects of `traceᴹ` are explicit because `_+_` is a
-- coproduct *projection*, not a constructor, so Agda cannot recover `X` from
-- the type of a machine `Machine (A + X) (B + X)`.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Level
import Relation.Binary.Construct.Closure.Equivalence as EqC

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
open MonoidalUtilities.Shorthands monoidal
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
-- The left-context law is derivable from the right one

-- `iter-ctx` puts an untouched context factor on the left of the state; the
-- braiding moves it to the right, and uniformity along that state map carries
-- it back.
iter-onL : {P Q A B : Obj} {u : P ⊗₀ A ⇒ P ⊗₀ (B + A)}
         → iter (onL {Q = Q} u) ≈ onL (iter u)
iter-onL {u = u} = begin
  iter (onL u)                          ≈˘⟨ cancelˡ σ⊗-inv ⟩
  σ⇒ ⊗₁ id ∘ (σ⇒ ⊗₁ id ∘ iter (onL u))  ≈˘⟨ refl⟩∘⟨ iter-uniform σ⇒ pure-σ⇒ (⟺ σ-onL) ⟩
  σ⇒ ⊗₁ id ∘ (iter (onR u) ∘ σ⇒ ⊗₁ id)  ≈⟨ refl⟩∘⟨ iter-ctx ⟩∘⟨refl ⟩
  σ⇒ ⊗₁ id ∘ (onR (iter u) ∘ σ⇒ ⊗₁ id)  ≈˘⟨ refl⟩∘⟨ σ-onL ⟩
  σ⇒ ⊗₁ id ∘ (σ⇒ ⊗₁ id ∘ onL (iter u))  ≈⟨ cancelˡ σ⊗-inv ⟩
  onL (iter u)                          ∎

------------------------------------------------------------------------
-- Yanking

-- The braiding's loop body exits on its first pass, so `iter` collapses after
-- one unfolding.  This is the make-or-break law of an iteration-induced trace,
-- and it is the cheap one.
private
  iter-σᴹ : {X : Obj} → iter (loopBody Iˢ X X X (step (σᴹ {X} {X}))) ≈ id
  iter-σᴹ = iter-fix ○ (refl⟩∘⟨ refl⟩∘⟨ (merge₂ʳ ○ refl⟩⊗⟨ inject₂))
          ○ (refl⟩∘⟨ δ⇐-i₁) ○ inject₁

  yank-step : {X : Obj} → traceStep Iˢ X X X (step (σᴹ {X} {X})) ≈ id
  yank-step {X} =
    (refl⟩∘⟨ (merge₂ʳ ○ refl⟩⊗⟨ inject₁)) ○ solve-i₂ Iˢ X X X _ ○ iter-σᴹ

yankingᴹ : {X : Obj} → traceᴹ X X X (σᴹ {X} {X}) ≲ idᴹ
yankingᴹ = mk-cong yank-step

------------------------------------------------------------------------
-- Vanishing on the unit

-- The loop wire is `⊥`, so the loop branch is a map out of the initial object
-- `St ⊗₀ ⊥` and never has to be inspected: `tstep-i₁` routes the input
-- straight past `solve`.
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

-- Both actions are functorial in the interface, which is all that is needed to
-- slide one past the dispatch; `iter-ctx` and the derived `iter-onL` slide it
-- past the loop.
onR-pre : {Y Z W : Obj} {w : Q ⊗₀ Y ⇒ Q ⊗₀ Z} (j : W ⇒ Y)
        → onR {P = P} w ∘ id ⊗₁ j ≈ onR (w ∘ id ⊗₁ j)
onR-pre j = (refl⟩∘⟨ ⟺ (onRᵍ-id⊗ j)) ○ ⟺ onRᵍ-∘

onL-pre : {Y Z W : Obj} {w : P ⊗₀ Y ⇒ P ⊗₀ Z} (j : W ⇒ Y)
        → onL {Q = Q} w ∘ id ⊗₁ j ≈ onL (w ∘ id ⊗₁ j)
onL-pre j = (refl⟩∘⟨ ⟺ (onL-str j)) ○ ⟺ onL-∘

module _ (S Q : State) (A B X : Obj) (k : obj S ⊗₀ (A + X) ⇒ obj S ⊗₀ (B + X)) where

  solve-onL : solve (S ⊛ Q) A B X (onL k) ≈ onL (solve S A B X k)
  solve-onL = δ-unique
    (solve-i₁ (S ⊛ Q) A B X (onL k)
       ○ ⟺ (onL-pre i₁ ○ onL-cong (solve-i₁ S A B X k) ○ onL-id))
    (solve-i₂ (S ⊛ Q) A B X (onL k) ○ iter-cong (onL-pre i₂) ○ iter-onL
       ○ ⟺ (onL-pre i₂ ○ onL-cong (solve-i₂ S A B X k)))

  traceStep-onL : traceStep (S ⊛ Q) A B X (onL k) ≈ onL (traceStep S A B X k)
  traceStep-onL = (solve-onL ⟩∘⟨ onL-pre i₁) ○ ⟺ onL-∘

module _ (P S : State) (A B X : Obj) (k : obj S ⊗₀ (A + X) ⇒ obj S ⊗₀ (B + X)) where

  solve-onR : solve (P ⊛ S) A B X (onR k) ≈ onR (solve S A B X k)
  solve-onR = δ-unique
    (solve-i₁ (P ⊛ S) A B X (onR k)
       ○ ⟺ (onR-pre i₁ ○ onR-cong (solve-i₁ S A B X k) ○ onR-id))
    (solve-i₂ (P ⊛ S) A B X (onR k) ○ iter-cong (onR-pre i₂) ○ iter-ctx
       ○ ⟺ (onR-pre i₂ ○ onR-cong (solve-i₂ S A B X k)))

  traceStep-onR : traceStep (P ⊛ S) A B X (onR k) ≈ onR (traceStep S A B X k)
  traceStep-onR = (solve-onR ⟩∘⟨ onR-pre i₁) ○ ⟺ onRᵍ-∘

------------------------------------------------------------------------
-- What is left

-- The swap of the last two summands, which `Traced`'s Fubini law is stated
-- with.
βᴹ : Machine ((A + B) + C) ((A + C) + B)
βᴹ = α⇐ᴹ ∘ᴹ (idᴹ ⊗ᵉ σᴹ) ∘ᴹ α⇒ᴹ

-- The four laws left for wave 2, as a record whose field TYPES typecheck: no
-- term in this file is an axiom, and a consumer takes the record as a module
-- parameter.
--
-- `trace-resp-≲` is asked in the *generator* form, which is the minimal
-- obligation: `trace-resp-≈ᴹ` below lifts it to the category's own equality.
-- It is the field on which the layer's axiom-freeness turns, and the one that
-- forced the hom equality to be a simulation: a behavioural equality relates
-- machines with no morphism between their state objects, and no base-level
-- `iter` law can then relate the two loops.  Discharging it is an instance of
-- `iter-uniform` at the simulation's own state map, which is why both are
-- restricted to `𝒫`.
record Remaining : Set (o ⊔ ℓ ⊔ e) where
  field
    trace-resp-≲ : {f g : Machine (A + X) (B + X)}
                 → f ≲ g → traceᴹ A B X f ≲ traceᴹ A B X g

    vanishing₂ : (f : Machine (A + (X + P)) (B + (X + P)))
               → traceᴹ A B X (traceᴹ (A + X) (B + X) P (α⇐ᴹ ∘ᴹ f ∘ᴹ α⇒ᴹ))
               ≈ᴹ traceᴹ A B (X + P) f

    superposing : (f : Machine (A + X) (B + X))
                → traceᴹ (P + A) (P + B) X (α⇐ᴹ ∘ᴹ (idᴹ {P} ⊗ᵉ f) ∘ᴹ α⇒ᴹ)
                ≈ᴹ (idᴹ {P} ⊗ᵉ traceᴹ A B X f)

    trace-comm : (f : Machine ((A + X) + P) ((B + X) + P))
               → traceᴹ A B X (traceᴹ (A + X) (B + X) P f)
               ≈ᴹ traceᴹ A B P (traceᴹ (A + P) (B + P) X (βᴹ ∘ᴹ f ∘ᴹ βᴹ))

  trace-resp-≈ᴹ : {f g : Machine (A + X) (B + X)}
                → f ≈ᴹ g → traceᴹ A B X f ≈ᴹ traceᴹ A B X g
  trace-resp-≈ᴹ = EqC.gmap (traceᴹ _ _ _) trace-resp-≲
