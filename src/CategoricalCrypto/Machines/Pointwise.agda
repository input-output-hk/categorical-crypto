{-# OPTIONS --safe --without-K --guardedness #-}

-- The `Kl(Dₚ)` point-level calculus machine steps are read with: simulations
-- along a function (`simFn`) and back (`fnStep`), and the paired point and the
-- state actions evaluated at a point.
-- It has no `GConstruction` in its closure, so a consumer of this calculus alone
-- does not pay for the trace.

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Construction.Kleisli.Discrete as KD
import Categories.Category.Construction.Kleisli.Discrete.Pure as KDP

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; swap)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pure

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.Machines.Pointwise where

module MC  = Core (𝒱ₚ 0ℓ)
module S   = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

module Cat = MCat (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
module T   = Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)
module V   = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
module K   = KD (Dₚ-DiscreteMonad {0ℓ})
module KP  = KDP (Dₚ-DiscreteMonad {0ℓ})

open import Categories.Category.Monoidal.Symmetric.Properties.Ext V.symmetric

private
  variable P Q X Y Z : Set

-- A state map applied to the state factor: the shape every `_≲_`'s `θ ⊗₁ id`
-- takes at a point, the state-side mirror of `Machines.Pure.pureᴵ`.
padϕ : (X → Y) → X × Z → Dₚ (Y × Z)
padϕ ϕ p = returnₚ (ϕ (proj₁ p) , proj₂ p)

⊗-pureˡ : (h : X → Y) (p : X × Z) → (K.pureᵏ h V.⊗₁ V.id) p ≈ₚ padϕ h p
⊗-pureˡ h p = >>=ₚ-identityˡ (h (proj₁ p)) _ ⟨≈⟩ >>=ₚ-identityˡ (proj₂ p) _

------------------------------------------------------------------------
-- Simulations along a function

-- A simulation along a function: a consumer supplies only the two pointwise laws.
simFn : {S T : MC.State} {k : MC.obj S × X → Dₚ (MC.obj S × Y)}
        {k′ : MC.obj T × X → Dₚ (MC.obj T × Y)} (h : MC.obj S → MC.obj T)
      → ((x : V.unit) → (MC.point S x >>=ₚ λ s → returnₚ (h s)) ≈ₚ MC.point T x)
      → ((p : MC.obj S × X) → (k p >>=ₚ padϕ h) ≈ₚ k′ (h (proj₁ p) , proj₂ p))
      → MC.mk S k S.≲ MC.mk T k′
simFn {k′ = k′} h hp hs = S.sim (K.pureᵏ h) (KP.structural h) hp λ p →
  bindᶠ (⊗-pureˡ h) ⟨≈⟩ hs p
  ⟨≈⟩ ≈sym (bindˣ (⊗-pureˡ h p) ⟨≈⟩ >>=ₚ-identityˡ (h (proj₁ p) , proj₂ p) k′)

-- The converse: a step law along a pure state map, read at a point.
fnStep : {k : P × X → Dₚ (P × Y)} {k′ : Q × X → Dₚ (Q × Y)} {θ : P → Dₚ Q} (θp : KP.IsPure θ)
       → V._≈_ (V._∘_ (θ V.⊗₁ V.id) k) (V._∘_ k′ (θ V.⊗₁ V.id))
       → (p : P × X) → (k p >>=ₚ padϕ (KP.fn θp)) ≈ₚ k′ (KP.fn θp (proj₁ p) , proj₂ p)
fnStep {P = P} {k′ = k′} {θ = θ} θp step p =
  bindᶠ (λ q → ≈sym (pad-fn q)) ⟨≈⟩ step p ⟨≈⟩ bindˣ (pad-fn p) ⟨≈⟩ >>=ₚ-identityˡ _ k′
  where
  pad-fn : {Z : Set} (q : P × Z) → (θ V.⊗₁ V.id) q ≈ₚ padϕ (KP.fn θp) q
  pad-fn (s , z) = bindˣ (KP.is-fn θp s) ⟨≈⟩ >>=ₚ-identityˡ (KP.fn θp s) _ ⟨≈⟩ >>=ₚ-identityˡ z _

------------------------------------------------------------------------
-- The paired point and the state actions, at a point

point-⊛ : (S T : MC.State) (x : V.unit)
        → MC.point (S MC.⊛ T) x
        ≈ₚ (MC.point S ttᵛ >>=ₚ λ a → MC.point T x >>=ₚ λ b → returnₚ (a , b))
point-⊛ S T x = >>=ₚ-identityˡ (ttᵛ , x) _

β-pt : (p : P) (q : Q) (x : X) → β ((p , q) , x) ≈ₚ returnₚ ((p , x) , q)
β-pt p q x =
  bindˣ (>>=ₚ-identityˡ (p , q , x) _ ⟨≈⟩ pureᴵ swap (p , q , x))
  ⟨≈⟩ >>=ₚ-identityˡ (p , x , q) _

onL-pt : (k : P × X → Dₚ (P × Y)) (p : P) (q : Q) (x : X)
       → MC.onL k ((p , q) , x)
       ≈ₚ (k (p , x) >>=ₚ λ r → returnₚ ((proj₁ r , q) , proj₂ r))
onL-pt k p q x =
  bindˣ (bindˣ (β-pt p q x) ⟨≈⟩ >>=ₚ-identityˡ ((p , x) , q) _
         ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ q _))
  ⟨≈⟩ >>=ₚ-assoc (k (p , x)) _ _
  ⟨≈⟩ bindᶠ (λ where (p′ , y) → >>=ₚ-identityˡ ((p′ , y) , q) _ ⟨≈⟩ β-pt p′ y q)

onR-pt : (k : Q × X → Dₚ (Q × Y)) (p : P) (q : Q) (x : X)
       → MC.onR k ((p , q) , x)
       ≈ₚ (k (q , x) >>=ₚ λ r → returnₚ ((p , proj₁ r) , proj₂ r))
onR-pt k p q x =
  bindˣ (>>=ₚ-identityˡ (p , q , x) _ ⟨≈⟩ >>=ₚ-identityˡ p _)
  ⟨≈⟩ >>=ₚ-assoc (k (q , x)) _ _
  ⟨≈⟩ bindᶠ (λ where (q′ , y) → >>=ₚ-identityˡ (p , q′ , y) _)
