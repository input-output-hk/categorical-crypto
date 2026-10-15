{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Machines.Positive.Base where

open import Categories.Category.Core
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Core
open import Categories.Category.Monoidal.Pure
open import Categories.Category.Monoidal.Traced
open import Categories.Monad.Discrete
import Categories.Category.Construction.Kleisli.Discrete as KD
import Categories.Category.Construction.Kleisli.Discrete.Distributive as KDD
import Categories.Category.Construction.Kleisli.Discrete.Pure as KDP
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Traced.Ext as TE

open import Data.Product.Base
open import Data.Sum.Base
open import Level
open import Relation.Binary.Bundles

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Commutative
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Positive.Monad
import ProbabilisticLogic.Dp.Positive.Iteration as PI
import ProbabilisticLogic.Dp.Positive.Transfer as PT

import CategoricalCrypto.Machines.Base as PM
import CategoricalCrypto.Machines.Bundle as Bundle
import CategoricalCrypto.Machines.G as G
import CategoricalCrypto.Machines.Iteration as Iteration
import CategoricalCrypto.Machines.Tensor as Tensor

private variable ℓ : Level

D₊-setoid : Set ℓ → Setoid ℓ ℓ
D₊-setoid A = record { Carrier = Dₚ A ; _≈_ = _≈₊_ ; isEquivalence = ≈₊-isEquivalence }

D₊-DiscreteMonad : DiscreteMonad ℓ
D₊-DiscreteMonad = record
  { elementwise = record
      { ≈ᴹ-setoid = D₊-setoid
      ; return = returnₚ
      ; _>>=_ = _>>=ₚ_
      ; >>=-cong = λ {_} {_} {x} {y} {f} {g} → bind-cong x y f g
      ; >>=-identityˡ-≈ = λ {_} {_} {a} {h} → ≈ₚ⇒≈₊ (>>=ₚ-identityˡ a h)
      ; >>=-identityʳ-≈ = λ d → ≈ₚ⇒≈₊ (>>=ₚ-identityʳ d)
      ; >>=-assoc-≈ = λ d {g} {h} → ≈ₚ⇒≈₊ (>>=ₚ-assoc d g h)
      }
  ; >>=-comm = λ {_} {_} {x} {y} → ≈ₚ⇒≈₊ (>>=ₚ-comm x y)
  }

𝒱₊ : (ℓ : Level) → SymmetricMonoidalCategory (suc ℓ) ℓ ℓ
𝒱₊ ℓ = KD.Klᴹ-SymmetricMonoidal (D₊-DiscreteMonad {ℓ})

dist₊ : (ℓ : Level) → MD.MonoidalDistributive (𝒱₊ ℓ)
dist₊ ℓ = KDD.MonoidalDistributiveᵏ (D₊-DiscreteMonad {ℓ})

𝒫₊ : (ℓ : Level) → PureSub (𝒱₊ ℓ)
𝒫₊ ℓ = KDP.PureSubᵏ (D₊-DiscreteMonad {ℓ})

module Elgotᵏ (ℓ : Level) where
  open DiscreteMonad (D₊-DiscreteMonad {ℓ})
  open KD (D₊-DiscreteMonad {ℓ})
  open KDP (D₊-DiscreteMonad {ℓ})
  open Tensor (𝒱₊ ℓ) (dist₊ ℓ) (𝒫₊ ℓ)
  open ≈ᴹ-Reasoning
  module Old = PM.Elgotᵏ ℓ
  module OldPure = KDP (PM.Dₚ-DiscreteMonad {ℓ})

  private variable S T A A′ B B′ : Set ℓ

  tstep-φ : {κ : S × A → Dₚ (T × A′)} {μ : S × B → Dₚ (T × B′)}
            (κᵖ : IsPure κ) (μᵖ : IsPure μ) (r : S × (B ⊎ A))
          → tstep μ κ r ≈ᴹ return (φ (fn κᵖ) (fn μᵖ) r)
  tstep-φ κᵖ μᵖ r = ≈₊-trans (tstep-cong (is-fn μᵖ) (is-fn κᵖ) r)
    (≈ₚ⇒≈₊ (Old.tstep-φ (OldPure.structural (fn κᵖ)) (OldPure.structural (fn μᵖ)) r))

  transfer : (κ : S × A → Dₚ (T × A′)) (μ : S × B → Dₚ (T × B′))
             (κᵖ : IsPure κ) (μᵖ : IsPure μ)
             {u : Body S A B} {v : Body T A′ B′}
           → (∀ sa → (κ sa >>= v) ≈ᴹ (u sa >>= tstep μ κ))
           → (sa : S × A) → (κ sa >>= iterₚ v) ≈ᴹ (iterₚ u sa >>= μ)
  transfer κ μ κᵖ μᵖ {u} {v} h sa = begin
    (κ sa >>= iterₚ v)
      ≈⟨ >>=-cong-x (is-fn κᵖ sa) ⟩
    (return (fn κᵖ sa) >>= iterₚ v)
      ≈⟨ >>=-identityˡ-≈ ⟩
    iterₚ v (fn κᵖ sa)
      ≈⟨ PT.iter-transfer u v (fn κᵖ) (fn μᵖ) sim sa ⟩
    mapₚ (fn μᵖ) (iterₚ u sa)
      ≈˘⟨ >>=-cong-f (is-fn μᵖ) ⟩
    (iterₚ u sa >>= μ) ∎
    where
    sim : ∀ sa′ → v (fn κᵖ sa′) ≈ᴹ mapₚ (φ (fn κᵖ) (fn μᵖ)) (u sa′)
    sim sa′ = begin
      v (fn κᵖ sa′)
        ≈˘⟨ >>=-identityˡ-≈ ⟩
      (return (fn κᵖ sa′) >>= v)
        ≈˘⟨ >>=-cong-x (is-fn κᵖ sa′) ⟩
      (κ sa′ >>= v)
        ≈⟨ h sa′ ⟩
      (u sa′ >>= tstep μ κ)
        ≈⟨ >>=-cong-f (tstep-φ κᵖ μᵖ) ⟩
      mapₚ (φ (fn κᵖ) (fn μᵖ)) (u sa′) ∎

Elgot₊ : (ℓ : Level) → Iteration.Elgot (𝒱₊ ℓ) (dist₊ ℓ) (𝒫₊ ℓ)
Elgot₊ ℓ = record
  { iter = iterₚ
  ; iter-cong = λ {u = u} {v = v} → PI.iter-cong u v
  ; iter-fix = λ sa → ≈ₚ⇒≈₊ (PM.Elgotᵏ.iter-fixₚ ℓ sa)
  ; iter-out = λ k sa → ≈ₚ⇒≈₊ (PM.Elgotᵏ.iter-outₚ ℓ k sa)
  ; iter-ctx = λ q → ≈ₚ⇒≈₊ (PM.Elgotᵏ.iter-ctxₚ ℓ q)
  ; iter-transfer = Elgotᵏ.transfer ℓ
  ; iter-cod = λ w sa → ≈ₚ⇒≈₊ (PM.Elgotᵏ.iter-codₚ ℓ w sa)
  ; pure-i₁ = structural inj₁
  ; pure-i₂ = structural inj₂
  ; pure-[] = []-pure
  }
  where open KDP (D₊-DiscreteMonad {ℓ})

ℳ₊ : (ℓ : Level) → SymmetricMonoidalCategory (suc ℓ) (suc ℓ) (suc ℓ)
ℳ₊ ℓ = Bundle.Mealy-SymmetricMonoidal (𝒱₊ ℓ) (dist₊ ℓ) (𝒫₊ ℓ)

Traced₊ : (ℓ : Level) → Traced (Bundle.Mealy-Monoidal (𝒱₊ ℓ) (dist₊ ℓ) (𝒫₊ ℓ))
Traced₊ ℓ = G.Mealy-Traced (𝒱₊ ℓ) (dist₊ ℓ) (𝒫₊ ℓ) (Elgot₊ ℓ)

TraceLaws₊ : (ℓ : Level) → TE.Laws (Traced₊ ℓ)
TraceLaws₊ ℓ = G.Mealy-TraceLaws (𝒱₊ ℓ) (dist₊ ℓ) (𝒫₊ ℓ) (Elgot₊ ℓ)

𝒢₊ᴹ : (ℓ : Level) → MonoidalCategory (suc ℓ) (suc ℓ) (suc ℓ)
𝒢₊ᴹ ℓ = G.Mealy-Gᴹ (𝒱₊ ℓ) (dist₊ ℓ) (𝒫₊ ℓ) (Elgot₊ ℓ)

𝒢₊ : (ℓ : Level) → Category (suc ℓ) (suc ℓ) (suc ℓ)
𝒢₊ ℓ = MonoidalCategory.U (𝒢₊ᴹ ℓ)
