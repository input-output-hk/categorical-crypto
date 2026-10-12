{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.UC.Machine.RelationalTests where

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Distributive as MD

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Bundles using (Equivalence)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Machines.Sim.Relational.Pointwise
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Machine.Relational

import CategoricalCrypto.Machines.Trace as Trace

private
  module G = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module Tr = Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)

open MD.MonoidalDistributive (distₚ 0ℓ) using (_+₁_)

tracked erased : (X : Set) → MC.Machine X X
tracked X = MC.mk (initˢ Bool false) λ { (b , x) → returnₚ (not b , x) }
erased X = MC.mk (initˢ ⊤ tt) λ { (_ , x) → returnₚ (tt , x) }

forget : ∀ X → tracked X S.≲ erased X
forget X = simFn (λ _ → tt) (λ _ → >>=ₚ-identityˡ false _) λ { (b , x) → >>=ₚ-identityˡ (not b , x) _ }

functional : ∀ X → tracked X S.≲ erased X
functional X = Equivalence.from RS.≲⇔≲[id] (Equivalence.to RS.≲⇔≲[id] (forget X))

graph : ∀ X → RS.RelSim V.id V.id V.id V.id (tracked X) (erased X)
graph X = RS.≲⇒relsim (forget X)

behaviour : tracked Bool ≈ᴿ erased Bool
behaviour = relsim⇒≈ᴿ (graph Bool)

summed : RS.RelSim (V.id +₁ V.id) (V.id +₁ V.id) (V.id +₁ V.id) (V.id +₁ V.id)
           (T._⊗ᵉ_ (tracked Bool) (tracked Bool)) (T._⊗ᵉ_ (erased Bool) (erased Bool))
summed = RS.⊗ᵉ-relsim (graph Bool) (graph Bool)

private
  sum-id : (V.id +₁ V.id) V.≈ (V.id {Bool ⊎ Bool})
  sum-id (inj₁ x) = >>=ₚ-identityˡ x _
  sum-id (inj₂ x) = >>=ₚ-identityˡ x _

feedback : RS.RelSim V.id V.id V.id V.id
             (Tr.traceᴹ Bool Bool Bool (tracked (Bool ⊎ Bool)))
             (Tr.traceᴹ Bool Bool Bool (erased (Bool ⊎ Bool)))
feedback = RS.trace-relsim (KP.structural (λ x → x)) (KP.structural (λ x → x))
  (KP.structural (λ x → x)) (KP.structural (λ x → x)) record
  { apex = RS.apex (graph (Bool ⊎ Bool))
  ; left = RS.≲[]-resp-≈ (V.Equiv.sym sum-id) (V.Equiv.sym sum-id) (RS.left (graph (Bool ⊎ Bool)))
  ; right = RS.≲[]-resp-≈ (V.Equiv.sym sum-id) (V.Equiv.sym sum-id) (RS.right (graph (Bool ⊎ Bool))) }

feedback-behaviour : Tr.traceᴹ Bool Bool Bool (tracked (Bool ⊎ Bool)) ≈ᴿ Tr.traceᴹ Bool Bool Bool (erased (Bool ⊎ Bool))
feedback-behaviour = relsim⇒≈ᴿ feedback

private
  μ = idᵐ {Bool , Bool}

G-compose : HSim μ μ
              (G._∘_ {Bool , Bool} {Bool , Bool} {Bool , Bool} G.id G.id)
              (G._∘_ {Bool , Bool} {Bool , Bool} {Bool , Bool} G.id G.id)
G-compose = HSim-∘ (HSim-id μ) (HSim-id μ)

G-tensor : HSim (μ ⊗ᵐ μ) (μ ⊗ᵐ μ)
             (G._⊗₁_ {Bool , Bool} {Bool , Bool} {Bool , Bool} {Bool , Bool} G.id G.id)
             (G._⊗₁_ {Bool , Bool} {Bool , Bool} {Bool , Bool} {Bool , Bool} G.id G.id)
G-tensor = HSim-⊗ (HSim-id μ) (HSim-id μ)
