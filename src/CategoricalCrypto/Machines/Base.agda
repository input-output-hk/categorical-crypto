{-# OPTIONS --safe --without-K --guardedness #-}

-- The base category the machine layer is meant to run over: the Kleisli
-- category of the probabilistic delay monad at discrete objects, symmetric
-- monoidal and distributive, with its Elgot iteration.
--
-- Objects are types and homs are `A → Dₚ B` up to `_≈ₚ_`.  Everything the
-- construction needs of the monad is the eight elementwise laws of
-- `DiscreteMonad`, commutativity included — which is what makes the Kleisli
-- category symmetric monoidal, and is the only place `Dₚ`'s Fubini identity is
-- spent.
--
-- `Dp.Iter.Body S A B` is literally `S ⊗₀ A ⇒ S ⊗₀ (B + A)` here and `_≈_` is
-- pointwise `_≈ₚ_`, so each law of `Elgot` is its elementwise witness from the
-- `Dp` iteration hierarchy modulo the `returnₚ` junctions the point-free
-- structural morphisms spend; absorbing those is all `Elgotᵏ` below does.

open import Categories.Category.Core
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Pure
open import Categories.Category.Monoidal.Traced
open import Categories.Monad.Discrete
import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Kleisli.Discrete.Distributive as KDD
import Categories.Category.Kleisli.Discrete.Pure as KDP
import Categories.Category.Monoidal.Distributive as MD

open import Data.Product.Base
open import Data.Sum.Base
open import Level
open import Relation.Binary.Bundles

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Commutative
open import ProbabilisticLogic.Dp.Elgot
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Iter.Codiagonal
open import ProbabilisticLogic.Dp.Iter.Out

import CategoricalCrypto.Machines.Bundle as Bundle
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.G as G
import CategoricalCrypto.Machines.Iteration as Iteration
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Laws as Laws

module CategoricalCrypto.Machines.Base where

private variable ℓ : Level

Dₚ-setoid : Set ℓ → Setoid ℓ ℓ
Dₚ-setoid A = record
  { Carrier = Dₚ A
  ; _≈_ = _≈ₚ_
  ; isEquivalence = record
    { refl  = λ {d} → ≈ₚ-refl d
    ; sym   = λ {d} {e} → ≈ₚ-sym d e
    ; trans = λ {d} {e} {h} → ≈ₚ-trans d e h
    }
  }

Dₚ-DiscreteMonad : DiscreteMonad ℓ
Dₚ-DiscreteMonad = record
  { ≈ᴹ-setoid       = Dₚ-setoid
  ; return          = returnₚ
  ; _>>=_           = _>>=ₚ_
  ; >>=-cong        = λ {_} {_} {x} {y} {f} {g} → >>=ₚ-cong x y f g
  ; >>=-identityˡ-≈ = λ {_} {_} {a} {h} → >>=ₚ-identityˡ a h
  ; >>=-identityʳ-≈ = >>=ₚ-identityʳ
  ; >>=-assoc-≈     = λ m {g} {h} → >>=ₚ-assoc m g h
  ; >>=-comm        = λ {_} {_} {x} {y} → >>=ₚ-comm x y
  }

𝒱ₚ : (ℓ : Level) → SymmetricMonoidalCategory (suc ℓ) ℓ ℓ
𝒱ₚ ℓ = KD.Klᴹ-SymmetricMonoidal (Dₚ-DiscreteMonad {ℓ})

distₚ : (ℓ : Level) → MD.MonoidalDistributive (𝒱ₚ ℓ)
distₚ ℓ = KDD.MonoidalDistributiveᵏ (Dₚ-DiscreteMonad {ℓ})

-- The pure state maps: `iterₚ` transfers along these and no others.
𝒫ₚ : (ℓ : Level) → PureSub (𝒱ₚ ℓ)
𝒫ₚ ℓ = KDP.PureSubᵏ (Dₚ-DiscreteMonad {ℓ})

module Elgotᵏ (ℓ : Level) where
  open DiscreteMonad (Dₚ-DiscreteMonad {ℓ})
  open KD (Dₚ-DiscreteMonad {ℓ})
  open KDD (Dₚ-DiscreteMonad {ℓ})
  open KDP (Dₚ-DiscreteMonad {ℓ})
  open MD.MonoidalDistributive (distₚ ℓ) using (δ⇒; _+₁_)
  open Core (𝒱ₚ ℓ)
  open Tensor (𝒱ₚ ℓ) (distₚ ℓ) (𝒫ₚ ℓ)
  open ≈ᴹ-Reasoning

  private variable A A′ B B′ C P S T X Y : Set ℓ
  private variable u : Body S A B

  --------------------------------------------------------------------
  -- The structural morphisms, computed

  onR-padₛ : (w : S × X → Dₚ (S × Y)) (c : P) (sx : S × X)
           → onR w (padₛ (c ,_) sx) ≈ᴹ mapₚ (padₛ (c ,_)) (w sx)
  onR-padₛ w c (s , x) = begin
    ((α⇒ᵏ ((c , s) , x) >>= (return ⊗ᵏ w)) >>= α⇐ᵏ)
      ≈⟨ >>=-cong-x >>=-identityˡ-≈ ⟩
    ((return ⊗ᵏ w) (c , s , x) >>= α⇐ᵏ)
      ≈⟨ ⊗ᵏ-expand return w α⇐ᵏ (c , s , x) ⟩
    (return c >>= λ a → w (s , x) >>= λ r → α⇐ᵏ (a , r))
      ≈⟨ >>=-identityˡ-≈ ⟩
    (w (s , x) >>= λ r → α⇐ᵏ (c , r))
      ≈⟨ >>=-cong-f (λ where (_ , _) → ≈ᴹ.refl) ⟩
    mapₚ (padₛ (c ,_)) (w (s , x)) ∎

  -- `undistribute` is exactly the case split `contᵢ` performs, so the two
  -- differ by the one junction `δ⇐` spends.
  δ⇐-contᵢ : (u : Body S A B) (r : S × (B ⊎ A))
           → (pureᵏ undistribute r >>= [ return , iterₚ u ]) ≈ᴹ contᵢ u r
  δ⇐-contᵢ u (_ , inj₁ _) = >>=-identityˡ-≈
  δ⇐-contᵢ u (_ , inj₂ _) = >>=-identityˡ-≈

  tstep-outκ : (k : S × B → Dₚ (S × C)) (r : S × (B ⊎ A))
             → tstep k return r ≈ᴹ outκ k r
  tstep-outκ k (s , inj₁ b) = begin
    ((return (inj₁ (s , b)) >>= (k +₁ return)) >>= δ⇒)
      ≈⟨ >>=-cong-x >>=-identityˡ-≈ ⟩
    ((inj₁ <$>ᴹ k (s , b)) >>= δ⇒)
      ≈⟨ <$>ᴹ->>= inj₁ (k (s , b)) δ⇒ ⟩
    (k (s , b) >>= λ sc → δ⇒ (inj₁ sc))
      ≈⟨ >>=-cong-f (λ where (_ , _) → ≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈) ⟩
    mapₚ inlₒ (k (s , b)) ∎
  tstep-outκ k (s , inj₂ p) = begin
    ((return (inj₂ (s , p)) >>= (k +₁ return)) >>= δ⇒)
      ≈⟨ >>=-cong-x (≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈) ⟩
    (return (inj₂ (s , p)) >>= δ⇒)
      ≈⟨ >>=-identityˡ-≈ ⟩
    δ⇒ (inj₂ (s , p))
      ≈⟨ ≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈ ⟩
    return (s , inj₂ p) ∎

  -- A `tstep` of two pure maps relabels a sum interface summandwise, which is
  -- exactly `Dp.Iter.φ`.
  tstep-φ : {κ : S × A → Dₚ (T × A′)} {μ : S × B → Dₚ (T × B′)}
            (κᵖ : IsPure κ) (μᵖ : IsPure μ) (r : S × (B ⊎ A))
          → tstep μ κ r ≈ᴹ return (φ (fn κᵖ) (fn μᵖ) r)
  tstep-φ {κ = κ} {μ} κᵖ μᵖ (s , inj₁ b) = begin
    ((return (inj₁ (s , b)) >>= (μ +₁ κ)) >>= δ⇒)
      ≈⟨ >>=-cong-x >>=-identityˡ-≈ ⟩
    ((μ (s , b) >>= pureᵏ inj₁) >>= δ⇒)
      ≈⟨ >>=-cong-x (≈ᴹ.trans (>>=-cong-x (is-fn μᵖ (s , b))) >>=-identityˡ-≈) ⟩
    (return (inj₁ (fn μᵖ (s , b))) >>= δ⇒)
      ≈⟨ >>=-identityˡ-≈ ⟩
    δ⇒ (inj₁ (fn μᵖ (s , b)))
      ≈⟨ ≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈ ⟩
    return (φ (fn κᵖ) (fn μᵖ) (s , inj₁ b)) ∎
  tstep-φ {κ = κ} {μ} κᵖ μᵖ (s , inj₂ p) = begin
    ((return (inj₂ (s , p)) >>= (μ +₁ κ)) >>= δ⇒)
      ≈⟨ >>=-cong-x >>=-identityˡ-≈ ⟩
    ((κ (s , p) >>= pureᵏ inj₂) >>= δ⇒)
      ≈⟨ >>=-cong-x (≈ᴹ.trans (>>=-cong-x (is-fn κᵖ (s , p))) >>=-identityˡ-≈) ⟩
    (return (inj₂ (fn κᵖ (s , p))) >>= δ⇒)
      ≈⟨ >>=-identityˡ-≈ ⟩
    δ⇒ (inj₂ (fn κᵖ (s , p)))
      ≈⟨ ≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈ ⟩
    return (φ (fn κᵖ) (fn μᵖ) (s , inj₂ p)) ∎

  ∇-flat : (r : S × ((B ⊎ A) ⊎ A))
         → (return ⊗ᵏ [ return , pureᵏ inj₂ ]) r ≈ᴹ return (flat r)
  ∇-flat (_ , inj₁ _) = ≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈
  ∇-flat (_ , inj₂ _) = ≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈

  --------------------------------------------------------------------
  -- The laws

  iter-congₚ : {v : Body S A B} → (∀ sa → u sa ≈ᴹ v sa)
             → (sa : S × A) → iterₚ u sa ≈ᴹ iterₚ v sa
  iter-congₚ {u = u} {v} = iterₚ-cong u v

  iter-fixₚ : (sa : S × A)
            → iterₚ u sa ≈ᴹ ((u sa >>= pureᵏ undistribute) >>= [ return , iterₚ u ])
  iter-fixₚ {u = u} sa = begin
    iterₚ u sa
      ≈⟨ iterₚ-fix u sa ⟩
    (u sa >>= contᵢ u)
      ≈˘⟨ >>=-cong-f (δ⇐-contᵢ u) ⟩
    (u sa >>= λ r → pureᵏ undistribute r >>= [ return , iterₚ u ])
      ≈˘⟨ >>=-assoc-≈ (u sa) ⟩
    ((u sa >>= pureᵏ undistribute) >>= [ return , iterₚ u ]) ∎

  iter-outₚ : (k : S × B → Dₚ (S × C)) (sa : S × A)
            → (iterₚ u sa >>= k) ≈ᴹ iterₚ (λ sa′ → u sa′ >>= tstep k return) sa
  iter-outₚ {u = u} k sa = begin
    (iterₚ u sa >>= k)
      ≈⟨ iterₚ-out u k sa ⟩
    iterₚ (bodyₒ u k) sa
      ≈⟨ iter-congₚ (λ _ → >>=-cong-f λ r → ≈ᴹ.sym (tstep-outκ k r)) sa ⟩
    iterₚ (λ sa′ → u sa′ >>= tstep k return) sa ∎

  iter-ctxₚ : (q : (P × S) × A) → iterₚ (onR u) q ≈ᴹ onR (iterₚ u) q
  iter-ctxₚ {u = u} ((c , s) , x) = begin
    iterₚ (onR u) ((c , s) , x)
      ≈⟨ iterₚ-ctx u (onR u) (onR-padₛ u) c (s , x) ⟩
    mapₚ (padₛ (c ,_)) (iterₚ u (s , x))
      ≈˘⟨ onR-padₛ (iterₚ u) c (s , x) ⟩
    onR (iterₚ u) ((c , s) , x) ∎

  iter-transferₚ : (κ : S × A → Dₚ (T × A′)) (μ : S × B → Dₚ (T × B′))
                   (κᵖ : IsPure κ) (μᵖ : IsPure μ)
                   {u : Body S A B} {v : Body T A′ B′}
                 → (∀ sa → (κ sa >>= v) ≈ᴹ (u sa >>= tstep μ κ))
                 → (sa : S × A) → (κ sa >>= iterₚ v) ≈ᴹ (iterₚ u sa >>= μ)
  iter-transferₚ κ μ κᵖ μᵖ {u} {v} h sa = begin
    (κ sa >>= iterₚ v)
      ≈⟨ >>=-cong-x (is-fn κᵖ sa) ⟩
    (return (fn κᵖ sa) >>= iterₚ v)
      ≈⟨ >>=-identityˡ-≈ ⟩
    iterₚ v (fn κᵖ sa)
      ≈⟨ iterₚ-transfer u v (fn κᵖ) (fn μᵖ) sim sa ⟩
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

  iter-codₚ : (w : Body S A (B ⊎ A)) (sa : S × A)
            → iterₚ (iterₚ w) sa
            ≈ᴹ iterₚ (λ sa′ → w sa′ >>= (return ⊗ᵏ [ return , pureᵏ inj₂ ])) sa
  iter-codₚ w sa = begin
    iterₚ (iterₚ w) sa
      ≈⟨ iterₚ-codiagonal w sa ⟩
    iterₚ (λ sa′ → mapₚ flat (w sa′)) sa
      ≈⟨ iter-congₚ (λ _ → >>=-cong-f λ r → ≈ᴹ.sym (∇-flat r)) sa ⟩
    iterₚ (λ sa′ → w sa′ >>= (return ⊗ᵏ [ return , pureᵏ inj₂ ])) sa ∎

Elgotₚ : (ℓ : Level) → Iteration.Elgot (𝒱ₚ ℓ) (distₚ ℓ) (𝒫ₚ ℓ)
Elgotₚ ℓ = record
  { iter          = iterₚ
  ; iter-cong     = iter-congₚ
  ; iter-fix      = iter-fixₚ
  ; iter-out      = iter-outₚ
  ; iter-ctx      = iter-ctxₚ
  ; iter-transfer = iter-transferₚ
  ; iter-cod      = iter-codₚ
  ; pure-i₁       = structural inj₁
  ; pure-i₂       = structural inj₂
  ; pure-[]       = []-pure
  }
  where
  open Elgotᵏ ℓ
  open KDP (Dₚ-DiscreteMonad {ℓ})

-- The ⊕-trace's four laws at the intended base: `Remaining` is a term with no
-- hypotheses under it, which is what makes the whole machine layer axiom-free.
Remainingₚ : (ℓ : Level) → Trace.Remaining (𝒱ₚ ℓ) (distₚ ℓ) (𝒫ₚ ℓ) (Elgotₚ ℓ)
Remainingₚ ℓ = Laws.Remainingᴹ (𝒱ₚ ℓ) (distₚ ℓ) (𝒫ₚ ℓ) (Elgotₚ ℓ)

------------------------------------------------------------------------
-- The machine category

-- Probabilistic Mealy machines under interface composition, with simulation as
-- the hom equality: symmetric monoidal in the interface sum, traced by the
-- ⊕-trace, and hypothesis-free.
ℳₚ : (ℓ : Level) → SymmetricMonoidalCategory (suc ℓ) (suc ℓ) (suc ℓ)
ℳₚ ℓ = Bundle.Mealy-SymmetricMonoidal (𝒱ₚ ℓ) (distₚ ℓ) (𝒫ₚ ℓ)

Tracedₚ : (ℓ : Level) → Traced (Bundle.Mealy-Monoidal (𝒱ₚ ℓ) (distₚ ℓ) (𝒫ₚ ℓ))
Tracedₚ ℓ = G.Mealy-Traced (𝒱ₚ ℓ) (distₚ ℓ) (𝒫ₚ ℓ) (Elgotₚ ℓ)

-- States and processes over `ℳₚ`: `GConstruction` instantiated unchanged.
𝒢ₚ : (ℓ : Level) → Category (suc ℓ) (suc ℓ) (suc ℓ)
𝒢ₚ ℓ = G.Mealy-G (𝒱ₚ ℓ) (distₚ ℓ) (𝒫ₚ ℓ) (Elgotₚ ℓ)
