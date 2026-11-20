{-# OPTIONS --safe --without-K #-}

import Categories.Category.Monoidal.Braided.Properties as BraidedProps
open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.CoproductTrace as CT
import Categories.Category.Monoidal.CoproductTrace.Context as CTC
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Distributive.Context as MDC
import Categories.Category.Monoidal.Distributive.Properties as MDP
open import Categories.Category.Monoidal.Subcategory
open import Categories.Category.Monoidal.Traced

import Relation.Binary.Construct.Closure.Equivalence as EqC

import CategoricalCrypto.Machines.Bundle as Bundle
import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.Machines.Trace {o ℓ e}
  (𝒱 : SymmetricMonoidalCategory o ℓ e) (dist : MD.MonoidalDistributive 𝒱)
  (𝒫 : WideSymmetricMonoidalSubcategory 𝒱) (E : CT.CoproductTrace 𝒱 dist 𝒫) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided
open Bundle 𝒱 dist 𝒫
open Core 𝒱
open Equiv
open MCat 𝒱 𝒫
open MD.MonoidalDistributive dist
open MDP 𝒱 dist
open WideSymmetricMonoidalSubcategory 𝒫
open Sim 𝒱 𝒫
open Tensor 𝒱 dist 𝒫

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric
open import Categories.Morphism.Reasoning U

private variable A B C X Y : Obj

module Context (S : State) = MDC 𝒱 dist (obj S)
module Tr (S : State) = CTC.At 𝒱 dist 𝒫 E (obj S)
module Feedback = CTC 𝒱 dist 𝒫 E

traceᴹ : (A B X : Obj) → Machine (A + X) (B + X) → Machine A B
traceᴹ A B X f = mk (state f) (Tr.trace (state f) (step f))

yankingᴹ : traceᴹ X X X σᴹ ≲ idᴹ
yankingᴹ = mk-cong (Tr.trace-resp-≈ Iˢ (⊗-[] i₂ i₁) ○ Tr.yanking Iˢ)

vanishing₁ᴹ : (f : Machine A B) → traceᴹ A B ⊥ (f ⊗ᵉ idᴹ) ≲ f
vanishing₁ᴹ f = collapseʳ (refl⟩∘⟨ (Tr.trace-resp-≈ (state f ⊛ Iˢ)
    (tstep-cong refl onR-id ○ ⟺ (Context.context-+₁ (state f ⊛ Iˢ) (onL (step f)) id))
    ○ Tr.vanishing₁ (state f ⊛ Iˢ)) ○ onL-collapseʳ)

traceStep-onL : (S Q : State) (k : obj S ⊗₀ (A + X) ⇒ obj S ⊗₀ (B + X))
              → Tr.trace (S ⊛ Q) (onL k) ≈ onL (Tr.trace S k)
traceStep-onL S Q k =
  insertˡ σ⊗-inv ○ refl⟩∘⟨ Feedback.trace-state σ⇒ selected-σ⇒ σ-onL
  ○ refl⟩∘⟨ Feedback.trace-frame (obj Q) (obj S) k ⟩∘⟨refl ○ refl⟩∘⟨ ⟺ σ-onL ○ cancelˡ σ⊗-inv

trace-resp-≲ : {f g : Machine (A + X) (B + X)} → f ≲ g → traceᴹ A B X f ≲ traceᴹ A B X g
trace-resp-≲ s = sim (θ s) (θ-selected s) (θ-point s) (Feedback.trace-state (θ s) (θ-selected s) (θ-step s))

trace-resp-≈ᴹ : {f g : Machine (A + X) (B + X)} → f ≈ᴹ g → traceᴹ A B X f ≈ᴹ traceᴹ A B X g
trace-resp-≈ᴹ = EqC.gmap (traceᴹ _ _ _) trace-resp-≲

vanishing₂ : (f : Machine (A + (X + Y)) (B + (X + Y)))
           → traceᴹ A B X (traceᴹ (A + X) (B + X) Y (α⇐ᴹ ∘ᴹ f ∘ᴹ α⇒ᴹ)) ≈ᴹ traceᴹ A B (X + Y) f
vanishing₂ f = ≲⇒≈ᴹ (≲-trans (trace-resp-≲ (trace-resp-≲ (pure-∘both +-assocʳ +-assocˡ f)))
                             (mk-cong (Feedback.vanish-step (St f) (step f))))

opaque
  unfolding _∘ᴹ_

  trace-∘ˡ : (g : Machine B C) (f : Machine (A + X) (B + X))
           → traceᴹ A C X (g ⊗ᵉ idᴹ ∘ᴹ f) ≈ᴹ g ∘ᴹ traceᴹ A B X f
  trace-∘ˡ g f = ≲⇒≈ᴹ (≲-trans (trace-resp-≲ (∘ᴹ-resp-≲ (⊗idᵉ-collapse g) ≲-refl))
    (mk-cong (Tr.trace-resp-≈ S
      ((onL-tstep ○ tstep-cong refl onL-id ○ ⟺ (Context.context-+₁ S (onL (step g)) id)) ⟩∘⟨refl)
      ○ Tr.tightenₗ S ○ refl⟩∘⟨ Feedback.trace-frame (St g) (St f) (step f))))
    where
      S : State
      S = state g ⊛ state f

  trace-∘ʳ : (f : Machine (A + X) (B + X)) (h : Machine C A)
           → traceᴹ C B X (f ∘ᴹ h ⊗ᵉ idᴹ) ≈ᴹ traceᴹ A B X f ∘ᴹ h
  trace-∘ʳ f h = ≲⇒≈ᴹ (≲-trans (trace-resp-≲ (∘ᴹ-resp-≲ ≲-refl (⊗idᵉ-collapse h)))
    (mk-cong (Tr.trace-resp-≈ S
      (refl⟩∘⟨ (onR-tstep ○ tstep-cong refl onR-id ○ ⟺ (Context.context-+₁ S (onR (step h)) id)))
      ○ Tr.tightenᵣ S ○ traceStep-onL (state f) (state h) (step f) ⟩∘⟨refl)))
    where
      S : State
      S = state f ⊛ state h

  slideᴹ : (f : Machine (A + X) (B + Y)) (g : Machine Y X)
         → traceᴹ A B Y (f ∘ᴹ idᴹ ⊗ᵉ g) ≈ᴹ traceᴹ A B X (idᴹ ⊗ᵉ g ∘ᴹ f)
  slideᴹ f g = ≲⇒≈ᴹ (trace-resp-≲ (∘ᴹ-resp-≲ ≲-refl (id⊗ᵉ-collapse g)))
    ○ᴹ ≲⇒≈ᴹ (mk-cong (Tr.trace-resp-≈ S
      (refl⟩∘⟨ (onR-tstep ○ tstep-cong onR-id refl ○ ⟺ (Context.context-+₁ S id (onR (step g)))))
      ○ Tr.slide S ○ Tr.trace-resp-≈ S (Context.context-+₁ S id (onR (step g)) ⟩∘⟨refl)))
    ○ᴹ ≲⇒≈ᴹ (trace-resp-≲ (sim σ⇒ selected-σ⇒ (⊛-swap-point (state f) (state g)) exchange))
    ○ᴹ ≲⇒≈ᴹ˘ (trace-resp-≲ (∘ᴹ-resp-≲ (id⊗ᵉ-collapse g) ≲-refl))
    where
    S : State
    S = state f ⊛ state g
    exchange : σ⇒ ⊗₁ id ∘ tstep id (onR (step g)) ∘ onL (step f)
             ≈ (onL (tstep id (step g)) ∘ onR (step f)) ∘ σ⇒ ⊗₁ id
    exchange = glue′ (tstep-sim id-comm σ-onR) σ-onL
      ○ (⟺ (onL-tstep ○ tstep-cong onL-id refl) ⟩∘⟨refl) ⟩∘⟨refl

superposing : (f : Machine (A + X) (B + X))
            → traceᴹ (Y + A) (Y + B) X (α⇐ᴹ ∘ᴹ idᴹ ⊗ᵉ f ∘ᴹ α⇒ᴹ) ≈ᴹ idᴹ ⊗ᵉ traceᴹ A B X f
superposing f = ≲⇒≈ᴹ (≲-trans (trace-resp-≲ (pure-∘both +-assocʳ +-assocˡ M)) (mk-cong
  (Tr.trace-resp-≈ V (refl⟩∘⟨ (tstep-cong onL-id refl ⟩∘⟨refl))
  ○ Feedback.super-step (obj V) (onR (step f))
  ○ tstep-cong (⟺ onL-id) (Feedback.trace-frame unit (St f) (step f)))))
  where
    M = idᴹ ⊗ᵉ f
    V = state M

Mealy-Traced : Traced Mealy-Monoidal
Mealy-Traced = record
  { symmetric    = Mealy-Symmetric
  ; trace        = λ {X} {A} {B} → traceᴹ A B X
  ; trace-resp-≈ = trace-resp-≈ᴹ
  ; slide        = slideᴹ _ _
  ; tightenₗ     = trace-∘ˡ _ _
  ; tightenᵣ     = trace-∘ʳ _ _
  ; vanishing₁   = ≲⇒≈ᴹ (vanishing₁ᴹ _)
  ; vanishing₂   = vanishing₂ _
  ; superposing  = superposing _
  ; yanking      = ≲⇒≈ᴹ yankingᴹ
  }
