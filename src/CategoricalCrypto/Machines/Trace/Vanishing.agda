{-# OPTIONS --safe --without-K #-}

-- Vanishing: a loop over `X` wrapped around a loop over `P` is one loop over
-- `X + P`.
--
-- This is where the loop-variable half of `iter-transfer` is spent: the inner
-- and the outer loop run over different variables, and reindexing one to the
-- other along `i₁`/`i₂` is exactly what no state-only uniformity can do.  The
-- doubled loop is then collapsed by `iter-cod`, whose `∇ = [ id , i₂ ]` cancels
-- the sorting map `ψ` (`∇ψ`).  Everything else is ⊕-side bookkeeping: an
-- equation out of a distributed sum is its two branches (`δ-unique`), and
-- `[]-δ⇐` pushes a summandwise interface relabelling through the dispatch.

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Pure using (PureSub)
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP

import CategoricalCrypto.Machines.Category as Category
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Iteration as Iteration
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Congruence as Congruence

module CategoricalCrypto.Machines.Trace.Vanishing
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱)
  (E : Iteration.Elgot 𝒱 dist 𝒫) where

open SymmetricMonoidalCategory 𝒱
open Category 𝒱 𝒫
open Congruence 𝒱 dist 𝒫 E
open Core 𝒱
open Equiv
open Iteration.Elgot E
open MD.MonoidalDistributive dist
open CE U cocartesian
open MDP 𝒱 dist
open PureSub 𝒫
open Sim 𝒱 𝒫
open Tensor 𝒱 dist 𝒫
open Trace 𝒱 dist 𝒫 E

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B P X Z : Obj

------------------------------------------------------------------------
-- Two ⊕-side helpers

[]-δ⇐ : {S A₁ A₂ B₁ B₂ : Obj} {p : S ⊗₀ B₁ ⇒ Z} {t : S ⊗₀ B₂ ⇒ Z}
        (r : A₁ ⇒ B₁) (s : A₂ ⇒ B₂)
      → [ p , t ] ∘ δ⇐ ∘ id ⊗₁ (r +₁ s) ≈ [ p ∘ id ⊗₁ r , t ∘ id ⊗₁ s ] ∘ δ⇐
[]-δ⇐ r s = (refl⟩∘⟨ δ⇐-+₁) ○ sym-assoc ○ ([]∘+₁ ⟩∘⟨refl)
  where
    δ⇐-+₁ : δ⇐ ∘ id ⊗₁ (r +₁ s) ≈ (id ⊗₁ r +₁ id ⊗₁ s) ∘ δ⇐
    δ⇐-+₁ = δ-unique
      (pullʳ (merge₂ˡ ○ (refl⟩⊗⟨ +₁∘i₁) ○ split₂ˡ) ○ pullˡ δ⇐-i₁
       ○ ⟺ (pullʳ δ⇐-i₁ ○ +₁∘i₁))
      (pullʳ (merge₂ˡ ○ (refl⟩⊗⟨ +₁∘i₂) ○ split₂ˡ) ○ pullˡ δ⇐-i₂
       ○ ⟺ (pullʳ δ⇐-i₂ ○ +₁∘i₂))

private
  ν : B + X ⇒ B + (X + P)
  ν = id +₁ i₁

  -- `ψ` sorts an exit on `B + (X + P)` into "outer exit" and "outer loop".
  ψ : B + (X + P) ⇒ (B + (X + P)) + (X + P)
  ψ = (ν +₁ i₂) ∘ α+⇐

  -- The codiagonal of `iter-cod` collapses the sorting map.
  ∇ψ : [ id , i₂ ] ∘ ψ {B} {X} {P} ≈ id
  ∇ψ = sym-assoc ○ (∇ν ⟩∘⟨refl) ○ ⊕.associator.isoʳ
    where
      ∇ν : [ id , i₂ ] ∘ (ν {B} {X} {P} +₁ i₂) ≈ α+⇒
      ∇ν = +-unique₂
        (+-unique₂
          (assoc ○ assoc
           ○ (refl⟩∘⟨ (pullˡ +₁∘i₁ ○ assoc ○ (refl⟩∘⟨ (+₁∘i₁ ○ identityʳ))))
           ○ pullˡ inject₁ ○ identityˡ ○ ⟺ (assoc ○ α+⇒-i₁i₁))
          (assoc ○ assoc
           ○ (refl⟩∘⟨ (pullˡ +₁∘i₁ ○ assoc ○ (refl⟩∘⟨ +₁∘i₂)))
           ○ pullˡ inject₁ ○ identityˡ ○ ⟺ (assoc ○ α+⇒-i₁i₂)))
        (assoc ○ (refl⟩∘⟨ +₁∘i₂) ○ pullˡ inject₂ ○ ⟺ α+⇒-i₂)

------------------------------------------------------------------------
-- The step-level law

module _ (V : State) (A B X P : Obj)
         (k : obj V ⊗₀ (A + (X + P)) ⇒ obj V ⊗₀ (B + (X + P))) where

  private
    W : Obj
    W = obj V

    Y : Obj
    Y = X + P

    k′ : W ⊗₀ ((A + X) + P) ⇒ W ⊗₀ ((B + X) + P)
    k′ = id ⊗₁ α+⇐ ∘ (k ∘ id ⊗₁ α+⇒)

    solve′ : W ⊗₀ ((B + X) + P) ⇒ W ⊗₀ (B + X)
    solve′ = solve V (A + X) (B + X) P k′

    h : W ⊗₀ (A + X) ⇒ W ⊗₀ (B + X)
    h = traceStep V (A + X) (B + X) P k′

    b : W ⊗₀ Y ⇒ W ⊗₀ (B + Y)
    b = loopBody V A B Y k

    c : W ⊗₀ Y ⇒ W ⊗₀ ((B + X) + P)
    c = id ⊗₁ α+⇐ ∘ b

    q : W ⊗₀ Y ⇒ W ⊗₀ (B + X)
    q = solve′ ∘ c

    v : W ⊗₀ Y ⇒ W ⊗₀ (B + Y)
    v = id ⊗₁ ν ∘ q

    w : W ⊗₀ Y ⇒ W ⊗₀ ((B + Y) + Y)
    w = id ⊗₁ ψ ∘ b

    -- `α+⇒` merges the two nested injections into one: entering `k′` on the
    -- inner loop wire is entering `k` on the outer one.
    k′-enter : {j : Z ⇒ (A + X) + P} {j′ : Z ⇒ Y}
             → α+⇒ ∘ j ≈ i₂ ∘ j′ → k′ ∘ id ⊗₁ j ≈ c ∘ id ⊗₁ j′
    k′-enter e = assoc
               ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ (merge₂ˡ ○ (refl⟩⊗⟨ e) ○ split₂ˡ))
                           ○ sym-assoc))
               ○ sym-assoc

    k′-i₁i₁ : k′ ∘ id ⊗₁ (i₁ {A + X} {P} ∘ i₁ {A} {X})
            ≈ id ⊗₁ α+⇐ ∘ (k ∘ id ⊗₁ i₁ {A} {X + P})
    k′-i₁i₁ = assoc ○ (refl⟩∘⟨ pullʳ (merge₂ˡ ○ (refl⟩⊗⟨ α+⇒-i₁i₁)))

    k′-i₁i₂ : k′ ∘ id ⊗₁ (i₁ {A + X} {P} ∘ i₂ {A} {X}) ≈ c ∘ id ⊗₁ i₁ {X} {P}
    k′-i₁i₂ = k′-enter α+⇒-i₁i₂

    k′-i₂ : loopBody V (A + X) (B + X) P k′ ≈ c ∘ id ⊗₁ i₂ {X} {P}
    k′-i₂ = k′-enter α+⇒-i₂

    h-loop : loopBody V A B X h ≈ q ∘ id ⊗₁ i₁ {X} {P}
    h-loop = assoc ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ merge₂ˡ) ○ k′-i₁i₂)) ○ sym-assoc

    h-enter : h ∘ id ⊗₁ i₁ {A} {X} ≈ solve′ ∘ (id ⊗₁ α+⇐ ∘ (k ∘ id ⊗₁ i₁))
    h-enter = assoc ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ merge₂ˡ) ○ k′-i₁i₁))

    solve′-c : [ id , iter (c ∘ id ⊗₁ i₂ {X} {P}) ] ∘ δ⇐ ≈ solve′
    solve′-c = ⟺ ([]-cong₂ refl (iter-cong k′-i₂) ⟩∘⟨refl)

    w-enter : (j : Z ⇒ Y) → w ∘ id ⊗₁ j ≈ id ⊗₁ (ν +₁ i₂) ∘ (c ∘ id ⊗₁ j)
    w-enter j = ((split₂ˡ ⟩∘⟨refl) ⟩∘⟨refl) ○ (assoc ⟩∘⟨refl) ○ assoc

    q-i₂ : q ∘ id ⊗₁ i₂ {X} {P} ≈ iter (c ∘ id ⊗₁ i₂)
    q-i₂ = assoc ○ (refl⟩∘⟨ ⟺ k′-i₂) ○ ⟺ (solve-loop V (A + X) (B + X) P k′)
         ○ iter-cong k′-i₂

    iterw-i₂ : iter w ∘ id ⊗₁ i₂ {X} {P} ≈ id ⊗₁ ν ∘ iter (c ∘ id ⊗₁ i₂)
    iterw-i₂ = iter-transfer (id ⊗₁ i₂) (id ⊗₁ ν)
                 (pure-⊗₁ pure-id pure-i₂)
                 (pure-⊗₁ pure-id (pure-+₁ pure-id pure-i₁))
                 {u = c ∘ id ⊗₁ i₂} {v = w}
                 (w-enter i₂ ○ ⟺ (tstep-str ν i₂ ⟩∘⟨refl))

    iterw-i₁ : iter w ∘ id ⊗₁ i₁ {X} {P} ≈ id ⊗₁ ν ∘ (q ∘ id ⊗₁ i₁)
    iterw-i₁ = (iter-fix ⟩∘⟨refl) ○ assoc
             ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ w-enter i₁)))
             ○ (refl⟩∘⟨ sym-assoc) ○ sym-assoc
             ○ ([]-δ⇐ ν i₂ ⟩∘⟨refl)
             ○ (([]-cong₂ (identityˡ ○ ⟺ identityʳ) iterw-i₂ ⟩∘⟨refl) ⟩∘⟨refl)
             ○ ((⟺ ∘-distribˡ-[] ⟩∘⟨refl) ⟩∘⟨refl)
             ○ (assoc ⟩∘⟨refl) ○ assoc
             ○ (refl⟩∘⟨ (solve′-c ⟩∘⟨refl)) ○ (refl⟩∘⟨ sym-assoc)

    iterw : iter w ≈ v
    iterw = δ-unique (iterw-i₁ ○ ⟺ assoc)
                     (iterw-i₂ ○ ⟺ (assoc ○ (refl⟩∘⟨ q-i₂)))

    -- One loop over `X + P` after all: `∇ψ` cancels the sorting map.
    iterv : iter v ≈ iter b
    iterv = iter-cong (⟺ iterw) ○ iter-cod w ○ iter-cong collapse
      where
        collapse : id ⊗₁ [ id , i₂ ] ∘ w ≈ b
        collapse = sym-assoc ○ (merge₂ˡ ⟩∘⟨refl) ○ ((refl⟩⊗⟨ ∇ψ) ⟩∘⟨refl)
                 ○ (⊗.identity ⟩∘⟨refl) ○ identityˡ

    iterv-i₁ : iter v ∘ id ⊗₁ i₁ {X} {P} ≈ iter (q ∘ id ⊗₁ i₁)
    iterv-i₁ = iter-transfer (id ⊗₁ i₁) id (pure-⊗₁ pure-id pure-i₁) pure-id
                 {u = q ∘ id ⊗₁ i₁} {v = v} (assoc ○ ⟺ (tstep-ν ⟩∘⟨refl))
             ○ identityˡ
      where
        tstep-ν : tstep id (id ⊗₁ i₁ {X} {P}) ≈ id ⊗₁ ν
        tstep-ν = tstep-cong (⟺ ⊗.identity) refl ○ tstep-str id i₁

    solve-h : solve V A B X h ≈ [ id , iter (q ∘ id ⊗₁ i₁ {X} {P}) ] ∘ δ⇐
    solve-h = []-cong₂ refl (iter-cong h-loop) ⟩∘⟨refl

    iterv-i₂ : iter v ∘ id ⊗₁ i₂ {X} {P} ≈ solve V A B X h ∘ iter (c ∘ id ⊗₁ i₂)
    iterv-i₂ = (iter-fix ⟩∘⟨refl) ○ assoc
             ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ q-i₂)))))
             ○ (refl⟩∘⟨ sym-assoc) ○ sym-assoc
             ○ ([]-δ⇐ id i₁ ⟩∘⟨refl)
             ○ (([]-cong₂ (identityˡ ○ ⊗.identity) iterv-i₁ ⟩∘⟨refl) ⟩∘⟨refl)
             ○ ((⟺ solve-h) ⟩∘⟨refl)

    solve-nest : solve V A B X h ∘ (solve′ ∘ id ⊗₁ α+⇐) ≈ solve V A B Y k
    solve-nest = δ-unique branch₁ branch₂
      where
        branch₁ = (assoc ○ (refl⟩∘⟨ assoc)
                   ○ (refl⟩∘⟨ refl⟩∘⟨ (merge₂ˡ ○ (refl⟩⊗⟨ α+⇐-i₁) ○ split₂ˡ))
                   ○ (refl⟩∘⟨ sym-assoc)
                   ○ (refl⟩∘⟨ (solve-i₁ V (A + X) (B + X) P k′ ⟩∘⟨refl))
                   ○ (refl⟩∘⟨ identityˡ) ○ solve-i₁ V A B X h)
                ○ ⟺ (solve-i₁ V A B Y k)

        nested₁ = (assoc ○ (refl⟩∘⟨ assoc)
                   ○ (refl⟩∘⟨ refl⟩∘⟨ (merge₂ˡ ○ (refl⟩⊗⟨ +₁∘i₁) ○ split₂ˡ))
                   ○ (refl⟩∘⟨ sym-assoc)
                   ○ (refl⟩∘⟨ (solve-i₁ V (A + X) (B + X) P k′ ⟩∘⟨refl))
                   ○ (refl⟩∘⟨ identityˡ) ○ solve-i₂ V A B X h)
                ○ ⟺ (((⟺ iterv) ⟩∘⟨refl) ○ iterv-i₁ ○ ⟺ (iter-cong h-loop))

        nested₂ = (assoc ○ (refl⟩∘⟨ assoc)
                   ○ (refl⟩∘⟨ refl⟩∘⟨ (merge₂ˡ ○ (refl⟩⊗⟨ (+₁∘i₂ ○ identityʳ))))
                   ○ (refl⟩∘⟨ (solve-i₂ V (A + X) (B + X) P k′ ○ iter-cong k′-i₂)))
                ○ ⟺ (((⟺ iterv) ⟩∘⟨refl) ○ iterv-i₂)

        branch₂ = (assoc ○ (refl⟩∘⟨ assoc)
                   ○ (refl⟩∘⟨ refl⟩∘⟨ (merge₂ˡ ○ (refl⟩⊗⟨ α+⇐-i₂))))
                ○ δ-unique nested₁ nested₂
                ○ ⟺ (solve-i₂ V A B Y k)

  vanish-step : traceStep V A B X (traceStep V (A + X) (B + X) P
                  (id ⊗₁ α+⇐ ∘ (k ∘ id ⊗₁ α+⇒)))
              ≈ traceStep V A B (X + P) k
  vanish-step = (refl⟩∘⟨ h-enter) ○ (refl⟩∘⟨ sym-assoc) ○ sym-assoc
              ○ (solve-nest ⟩∘⟨refl)

------------------------------------------------------------------------
-- The machine-level law

vanishing₂ : {A B P X : Obj} (f : Machine (A + (X + P)) (B + (X + P)))
           → traceᴹ A B X (traceᴹ (A + X) (B + X) P (α⇐ᴹ ∘ᴹ f ∘ᴹ α⇒ᴹ))
           ≈ᴹ traceᴹ A B (X + P) f
vanishing₂ {A} {B} {P} {X} f = ≲⇒≈ᴹ
  (≲-trans (trace-resp-≲ {A} {B} {X} (trace-resp-≲ {A + X} {B + X} {P} reconcile))
           (mk-cong (vanish-step (state f) A B X P (step f))))
  where
    reconcile : (α⇐ᴹ ∘ᴹ f ∘ᴹ α⇒ᴹ)
              ≲ mk (state f) (id ⊗₁ α+⇐ ∘ (step f ∘ id ⊗₁ α+⇒))
    reconcile = ≲-trans (∘ᴹ-resp-≲ ≲-refl (pure-∘ʳ α+⇒ f))
                        (pure-∘ˡ α+⇐ (mk (state f) (step f ∘ id ⊗₁ α+⇒)))
