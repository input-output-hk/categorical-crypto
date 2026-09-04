{-# OPTIONS --safe --without-K #-}

-- Superposing: an interface summand `P` the traced machine never sees.
--
-- Both sides run at `Iˢ ⊛ state f`, so once the two `pureᴹ` re-bracketings are
-- absorbed into the step the law is a single step equation.  Its content is
-- `exit-relabel`: the superposed loop exits into `(P + B) + X` where the plain
-- one exits into `B + X`, and relabelling an exit branch is `iter-out` — the
-- only iteration field spent here.

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Properties as MDP

import CategoricalCrypto.Machines.Category as MC
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Iteration as Iteration
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Congruence as Congruence

module CategoricalCrypto.Machines.Trace.Superposing
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) (𝒫 : PureSub 𝒱)
  (E : Iteration.Elgot 𝒱 dist 𝒫) where

open SymmetricMonoidalCategory 𝒱
open Congruence 𝒱 dist 𝒫 E
open Core 𝒱
open Equiv
open Frame 𝒱
open Iteration.Elgot E
open MC 𝒱 𝒫
open MD.MonoidalDistributive dist
open CE U cocartesian
open MDP 𝒱 dist
open Sim 𝒱 𝒫
open Tensor 𝒱 dist 𝒫
open Trace 𝒱 dist 𝒫 E

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

------------------------------------------------------------------------
-- One step

super-step : (V : State) (P A B X : Obj) (g : obj V ⊗₀ (A + X) ⇒ obj V ⊗₀ (B + X))
           → traceStep V (P + A) (P + B) X (id ⊗₁ α+⇐ ∘ (tstep id g ∘ id ⊗₁ α+⇒))
           ≈ tstep id (traceStep V A B X g)
super-step V P A B X g = δ-unique branch₁ branch₂
  where
    k′ : obj V ⊗₀ ((P + A) + X) ⇒ obj V ⊗₀ ((P + B) + X)
    k′ = id ⊗₁ α+⇐ ∘ (tstep id g ∘ id ⊗₁ α+⇒)

    enter₁ : k′ ∘ id ⊗₁ (i₁ ∘ i₁) ≈ id ⊗₁ i₁ ∘ id ⊗₁ i₁
    enter₁ = assoc ○ (refl⟩∘⟨ assoc)
           ○ (refl⟩∘⟨ (refl⟩∘⟨ (merge₂ˡ ○ (refl⟩⊗⟨ α+⇒-i₁i₁))))
           ○ (refl⟩∘⟨ (tstep-i₁ ○ identityʳ))
           ○ merge₂ˡ ○ (refl⟩⊗⟨ α+⇐-i₁) ○ split₂ˡ

    enter₂ : {W : Obj} {j : W ⇒ (P + A) + X} {j′ : W ⇒ A + X} → α+⇒ ∘ j ≈ i₂ ∘ j′
           → k′ ∘ id ⊗₁ j ≈ id ⊗₁ (i₂ +₁ id) ∘ (g ∘ id ⊗₁ j′)
    enter₂ e = assoc ○ (refl⟩∘⟨ assoc)
             ○ (refl⟩∘⟨ (refl⟩∘⟨ (merge₂ˡ ○ (refl⟩⊗⟨ e) ○ split₂ˡ)))
             ○ (refl⟩∘⟨ pullˡ tstep-i₂) ○ (refl⟩∘⟨ assoc)
             ○ pullˡ (merge₂ˡ ○ (refl⟩⊗⟨ α+⇐-i₂))

    loop-relabel : loopBody V (P + A) (P + B) X k′
                 ≈ tstep (id ⊗₁ i₂) id ∘ loopBody V A B X g
    loop-relabel = enter₂ α+⇒-i₂
                 ○ (⟺ (tstep-cong refl (⟺ ⊗.identity) ○ tstep-str i₂ id) ⟩∘⟨refl)

    exit-relabel : solve V (P + A) (P + B) X k′ ∘ id ⊗₁ (i₂ +₁ id)
                 ≈ id ⊗₁ i₂ ∘ solve V A B X g
    exit-relabel = δ-unique
      ((assoc ○ (refl⟩∘⟨ (merge₂ˡ ○ (refl⟩⊗⟨ +₁∘i₁) ○ split₂ˡ))
        ○ pullˡ (solve-i₁ V (P + A) (P + B) X k′) ○ identityˡ)
       ○ ⟺ (assoc ○ (refl⟩∘⟨ solve-i₁ V A B X g) ○ identityʳ))
      ((assoc ○ (refl⟩∘⟨ (merge₂ˡ ○ (refl⟩⊗⟨ (+₁∘i₂ ○ identityʳ))))
        ○ solve-i₂ V (P + A) (P + B) X k′
        ○ iter-cong loop-relabel ○ ⟺ (iter-out (id ⊗₁ i₂)))
       ○ ⟺ (assoc ○ (refl⟩∘⟨ solve-i₂ V A B X g)))

    branch₁ = (assoc ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ merge₂ˡ))) ○ (refl⟩∘⟨ enter₁)
               ○ pullˡ (solve-i₁ V (P + A) (P + B) X k′) ○ identityˡ)
            ○ ⟺ (tstep-i₁ ○ identityʳ)

    branch₂ = (assoc ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ merge₂ˡ)))
               ○ (refl⟩∘⟨ enter₂ α+⇒-i₁i₂) ○ pullˡ exit-relabel ○ assoc)
            ○ ⟺ tstep-i₂

------------------------------------------------------------------------
-- The law

superposing : {A B P X : Obj} (f : Machine (A + X) (B + X))
            → traceᴹ (P + A) (P + B) X (α⇐ᴹ ∘ᴹ (idᴹ {P} ⊗ᵉ f) ∘ᴹ α⇒ᴹ)
            ≈ᴹ (idᴹ {P} ⊗ᵉ traceᴹ A B X f)
superposing {A} {B} {P} {X} f =
  ≲⇒≈ᴹ (≲-trans (trace-resp-≲ reconcile) (mk-cong step-eq))
  where
    M = idᴹ {P} ⊗ᵉ f
    V = state M

    k : obj V ⊗₀ ((P + A) + X) ⇒ obj V ⊗₀ (P + (B + X))
    k = step M ∘ id ⊗₁ α+⇒

    reconcile : (α⇐ᴹ ∘ᴹ M ∘ᴹ α⇒ᴹ) ≲ mk V (id ⊗₁ α+⇐ ∘ k)
    reconcile = ≲-trans (∘ᴹ-resp-≲ ≲-refl (pure-∘ʳ α+⇒ M)) (pure-∘ˡ α+⇐ (mk V k))

    step-eq : traceStep V (P + A) (P + B) X (id ⊗₁ α+⇐ ∘ k)
            ≈ step (idᴹ {P} ⊗ᵉ traceᴹ A B X f)
    step-eq = traceStep-cong V (P + A) (P + B) X
                (refl⟩∘⟨ (tstep-cong onL-id refl ⟩∘⟨refl))
            ○ super-step V P A B X (onR (step f))
            ○ tstep-cong (⟺ onL-id) (traceStep-onR Iˢ (state f) A B X (step f))
