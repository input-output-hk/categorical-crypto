{-# OPTIONS --safe --without-K --guardedness #-}

-- Function simulations and deterministic port retagging for the positive
-- quotient.  Retagging preserves the actual pure-simulation closure; no
-- endpoint-membership or discrete-state hypothesis is used.
module CategoricalCrypto.Machines.Positive.Pointwise where

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Construction.Kleisli.Discrete as KD
import Categories.Category.Construction.Kleisli.Discrete.Pure as KDP
open import Categories.Monad.Discrete
open import Data.Product.Base
open import Data.Unit.Polymorphic.Base
open import Level
open import Relation.Binary.PropositionalEquality using (refl)
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive.Monad
open import ProbabilisticLogic.Dp.Reasoning using (map-fuse)
open import CategoricalCrypto.Machines.Positive.Base
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Pointwise as Old
import CategoricalCrypto.Machines.Positive.Run as Run

module MC = Core (𝒱₊ 0ℓ)
module S = Sim (𝒱₊ 0ℓ) (𝒫₊ 0ℓ)
private
  module V = SymmetricMonoidalCategory (𝒱₊ 0ℓ)
  module K = KD (D₊-DiscreteMonad {0ℓ})
  module KP = KDP (D₊-DiscreteMonad {0ℓ})
  variable X Y X′ Y′ : Set

open DiscreteMonad (D₊-DiscreteMonad {0ℓ})
open ≈ᴹ-Reasoning

simFn : {U T : MC.State} {k : MC.obj U × X → Dₚ (MC.obj U × Y)}
        {k′ : MC.obj T × X → Dₚ (MC.obj T × Y)} (h : MC.obj U → MC.obj T)
      → ((x : V.unit) → mapₚ h (MC.point U x) ≈₊ MC.point T x)
      → ((p : MC.obj U × X) → (k p >>=ₚ Run.pad h) ≈₊ k′ (h (proj₁ p) , proj₂ p))
      → MC.mk U k S.≲ MC.mk T k′
simFn {k = k} {k′ = k′} h hp hs = S.sim (K.pureᵏ h) (KP.structural h) hp λ p → begin
  (k p >>=ₚ (K.pureᵏ h V.⊗₁ V.id))
    ≈⟨ >>=-cong-f (λ q → ≈ₚ⇒≈₊ (Old.⊗-pureˡ h q)) ⟩
  (k p >>=ₚ Run.pad h)
    ≈⟨ hs p ⟩
  k′ (h (proj₁ p) , proj₂ p)
    ≈˘⟨ ≈ₚ⇒≈₊ (>>=ₚ-identityˡ (h (proj₁ p) , proj₂ p) k′) ⟩
  (Run.pad h p >>=ₚ k′)
    ≈˘⟨ >>=-cong-x (≈ₚ⇒≈₊ (Old.⊗-pureˡ h p)) ⟩
  ((K.pureᵏ h V.⊗₁ V.id) p >>=ₚ k′) ∎

sandwichᴹ : MC.Machine X Y → (X′ → X) → (Y → Y′) → MC.Machine X′ Y′
sandwichᴹ f input output = MC.mk (MC.state f) λ p →
  mapₚ (λ r → proj₁ r , output (proj₂ r)) (MC.step f (proj₁ p , input (proj₂ p)))

module _ {f g : MC.Machine X Y} (input : X′ → X) (output : Y → Y′) (sim : f S.≲ g) where
  private
    h = Run.ϕ sim
    out-f : MC.St f × Y → MC.St f × Y′
    out-f r = proj₁ r , output (proj₂ r)
    out-g : MC.St g × Y → MC.St g × Y′
    out-g r = proj₁ r , output (proj₂ r)
    state : MC.St f × Y → MC.St g × Y
    state r = h (proj₁ r) , proj₂ r
    state′ : MC.St f × Y′ → MC.St g × Y′
    state′ r = h (proj₁ r) , proj₂ r
    both : MC.St f × Y → MC.St g × Y′
    both r = h (proj₁ r) , output (proj₂ r)

  sandwich-sim : sandwichᴹ f input output S.≲ sandwichᴹ g input output
  sandwich-sim = simFn h (λ { tt → Run.point-sim sim }) λ p → begin
    mapₚ state′ (mapₚ out-f (MC.step f (proj₁ p , input (proj₂ p))))
      ≈⟨ ≈ₚ⇒≈₊ (map-fuse (MC.step f (proj₁ p , input (proj₂ p))) out-f state′ both (λ _ → refl)) ⟩
    mapₚ both (MC.step f (proj₁ p , input (proj₂ p)))
      ≈˘⟨ ≈ₚ⇒≈₊ (map-fuse (MC.step f (proj₁ p , input (proj₂ p))) state out-g both (λ _ → refl)) ⟩
    mapₚ out-g (mapₚ state (MC.step f (proj₁ p , input (proj₂ p))))
      ≈⟨ map-cong out-g (Run.step-sim sim (proj₁ p , input (proj₂ p))) ⟩
    mapₚ out-g (MC.step g (h (proj₁ p) , input (proj₂ p))) ∎

sandwich-resp : (input : X′ → X) (output : Y → Y′) {f g : MC.Machine X Y}
               → f S.≈ᴹ g → sandwichᴹ f input output S.≈ᴹ sandwichᴹ g input output
sandwich-resp input output = EqC.gmap (λ f → sandwichᴹ f input output) (sandwich-sim input output)
