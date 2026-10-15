{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Machines.Positive.Run where

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Construction.Kleisli.Discrete as KD
import Categories.Category.Construction.Kleisli.Discrete.Pure as KDP
open import Categories.Monad.Discrete

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Unit.Polymorphic.Base
open import Level
open import Relation.Binary using (IsEquivalence)
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Positive.Monad
open import ProbabilisticLogic.Dp.Reasoning using (bind-map)

open import CategoricalCrypto.Machines.Positive.Base
open import CategoricalCrypto.Strategy
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

private
  module MC = Core (𝒱₊ 0ℓ)
  module S = Sim (𝒱₊ 0ℓ) (𝒫₊ 0ℓ)
  module P = KDP (D₊-DiscreteMonad {0ℓ})
  module V = SymmetricMonoidalCategory (𝒱₊ 0ℓ)
  variable X Y Z : Set

open DiscreteMonad (D₊-DiscreteMonad {0ℓ})
open ≈ᴹ-Reasoning

pad : (X → Y) → X × Z → Dₚ (Y × Z)
pad f (x , z) = returnₚ (f x , z)

module _ (M : MC.Machine X Y) where
  runFrom : MC.St M → Strat X Y → Dₚ Bool
  runFrom s (out b) = returnₚ b
  runFrom s (coin μ k) = coinₚ μ >>=ₚ λ b → runFrom s (k b)
  runFrom s (ask i k) = MC.step M (s , i) >>=ₚ λ r → runFrom (proj₁ r) (k (proj₂ r))

  run : Strat X Y → Dₚ Bool
  run d = MC.point (MC.state M) tt >>=ₚ λ s → runFrom s d

module _ {f g : MC.Machine X Y} (ϕ : MC.St f → MC.St g)
  (step-law : ∀ p → (MC.step f p >>=ₚ pad ϕ) ≈₊ MC.step g (ϕ (proj₁ p) , proj₂ p)) where

  from-resp : (s : MC.St f) (d : Strat X Y) → runFrom f s d ≈₊ runFrom g (ϕ s) d
  from-resp s (out b) = ≈₊-refl
  from-resp s (coin μ k) = >>=-cong-f (λ b → from-resp s (k b))
  from-resp s (ask i k) = begin
    (MC.step f (s , i) >>=ₚ λ r → runFrom f (proj₁ r) (k (proj₂ r)))
      ≈⟨ >>=-cong-f (λ r → from-resp (proj₁ r) (k (proj₂ r))) ⟩
    (MC.step f (s , i) >>=ₚ λ r → runFrom g (ϕ (proj₁ r)) (k (proj₂ r)))
      ≈˘⟨ >>=-cong-f (λ r → ≈ₚ⇒≈₊ (>>=ₚ-identityˡ (ϕ (proj₁ r) , proj₂ r) _)) ⟩
    (MC.step f (s , i) >>=ₚ λ r → pad ϕ r >>=ₚ λ q → runFrom g (proj₁ q) (k (proj₂ q)))
      ≈˘⟨ ≈ₚ⇒≈₊ (>>=ₚ-assoc (MC.step f (s , i)) (pad ϕ) _) ⟩
    ((MC.step f (s , i) >>=ₚ pad ϕ) >>=ₚ λ q → runFrom g (proj₁ q) (k (proj₂ q)))
      ≈⟨ >>=-cong-x (step-law (s , i)) ⟩
    runFrom g (ϕ s) (ask i k) ∎

module _ {f g : MC.Machine X Y} (sim : f S.≲ g) where
  ϕ : MC.St f → MC.St g
  ϕ = P.fn (S.θ-pure sim)

  pad-fn : {Z : Set} (q : MC.St f × Z) → (S.θ sim V.⊗₁ V.id) q ≈₊ pad ϕ q
  pad-fn (s , z) = begin
    (S.θ sim V.⊗₁ V.id) (s , z)
      ≈⟨ >>=-cong-x (P.is-fn (S.θ-pure sim) s) ⟩
    (returnₚ (ϕ s) >>=ₚ λ t → returnₚ z >>=ₚ λ z′ → returnₚ (t , z′))
      ≈⟨ ≈ₚ⇒≈₊ (>>=ₚ-identityˡ (ϕ s) _) ⟩
    (returnₚ z >>=ₚ λ z′ → returnₚ (ϕ s , z′))
      ≈⟨ ≈ₚ⇒≈₊ (>>=ₚ-identityˡ z _) ⟩
    pad ϕ (s , z) ∎

  step-sim : ∀ p → (MC.step f p >>=ₚ pad ϕ) ≈₊ MC.step g (ϕ (proj₁ p) , proj₂ p)
  step-sim p = ≈₊-trans (>>=-cong-f (λ q → ≈₊-sym (pad-fn q)))
    (≈₊-trans (S.θ-step sim p) (≈₊-trans (>>=-cong-x (pad-fn p)) (≈ₚ⇒≈₊ (>>=ₚ-identityˡ _ (MC.step g)))))

  point-sim : mapₚ ϕ (MC.point (MC.state f) tt) ≈₊ MC.point (MC.state g) tt
  point-sim = ≈₊-trans (>>=-cong-f (λ s → ≈₊-sym (P.is-fn (S.θ-pure sim) s))) (S.θ-point sim tt)

  run-sim : (d : Strat X Y) → run f d ≈₊ run g d
  run-sim d = ≈₊-trans (>>=-cong-f (λ s → from-resp ϕ step-sim s d))
    (≈₊-trans (≈₊-sym (≈ₚ⇒≈₊ (bind-map (MC.point (MC.state f) tt) ϕ (λ s → runFrom g s d))))
      (>>=-cong-x point-sim))

opaque
  run-resp : {f g : MC.Machine X Y} → f S.≈ᴹ g → (d : Strat X Y) → run f d ≈₊ run g d
  run-resp = EqC.fold (record
    { refl = λ _ → ≈₊-refl
    ; sym = λ h d → ≈₊-sym (h d)
    ; trans = λ h k d → ≈₊-trans (h d) (k d)
    }) run-sim
