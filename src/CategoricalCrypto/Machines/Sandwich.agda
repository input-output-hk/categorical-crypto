{-# OPTIONS --safe --without-K --guardedness #-}

-- A machine with its interface renamed on both sides, same state.  This is the
-- shape a wire's absorption leaves (`UC.Machine.Wire`), and `squeeze` is its
-- pointwise content: a machine between two PURE interface relabellings is that
-- machine, renamed.

open import Categories.Category.Monoidal.Bundle
open import Categories.Monad.Discrete
import Categories.Category.Construction.Kleisli.Discrete as KD

open import Data.Product.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pure

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Machines.Sandwich where

private
  module 𝒱 = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)

open Core (𝒱ₚ 0ℓ)
open KD (Dₚ-DiscreteMonad {0ℓ})
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

open import Categories.Category.Monoidal.Reasoning 𝒱.monoidal

private
  variable X Y X′ Y′ X″ Y″ : Set

-- The machine `f` with its interface renamed: `i` on the way in, `o` on the
-- way out, `f`'s own state kept.
sandwichᴹ : Machine X Y → (X′ → X) → (Y → Y′) → Machine X′ Y′
sandwichᴹ f i o = mk (state f)
  λ p → mapₚ (λ q → proj₁ q , o (proj₂ q)) (step f (proj₁ p , i (proj₂ p)))

-- Two renamings in a row are one.
sandwich-∘ : (f : Machine X Y) (i : X′ → X) (o : Y → Y′) (i′ : X″ → X′) (o′ : Y′ → Y″)
           → sandwichᴹ (sandwichᴹ f i o) i′ o′
             ≈ᴹ sandwichᴹ f (λ x → i (i′ x)) (λ y → o′ (o y))
sandwich-∘ f i o i′ o′ =
  ≲⇒≈ᴹ (mk-cong λ p → map-map (step f (proj₁ p , i (i′ (proj₂ p)))) _ _)

-- A renaming by identities is no renaming.
sandwich-id : (f : Machine X Y) (i : X → X) (o : Y → Y)
            → ((z : X) → i z ≡ z) → ((w : Y) → o w ≡ w)
            → sandwichᴹ f i o ≈ᴹ f
sandwich-id f i o ei eo = ≲⇒≈ᴹ (mk-cong pt)
  where
  pt : (p : _) → _
  pt (s , z) = ≡⇒≈ₚ (cong (λ w → mapₚ (λ q → proj₁ q , o (proj₂ q)) (step f (s , w))) (ei z))
           ⟨≈⟩ map-eq (step f (s , z)) _ (λ q → q)
                      (λ q → cong (proj₁ q ,_) (eo (proj₂ q)))
           ⟨≈⟩ >>=ₚ-identityʳ (step f (s , z))

-- The pointwise content of a wire's absorption.
squeeze : (f : Machine X Y) (h : X′ → X) (k : Y → Y′)
          {H : 𝒱._⇒_ X′ X} {K : 𝒱._⇒_ Y Y′}
        → 𝒱._≈_ H (pureᵏ h) → 𝒱._≈_ K (pureᵏ k)
        → mk (state f) (𝒱._∘_ (𝒱._⊗₁_ 𝒱.id K) (𝒱._∘_ (step f) (𝒱._⊗₁_ 𝒱.id H)))
          ≈ᴹ sandwichᴹ f h k
squeeze f h k {H} {K} eH eK = ≲⇒≈ᴹ (mk-cong pt)
  where
  -- Both paddings are ascribed: left to inference, the identity factor of
  -- `refl⟩⊗⟨` is a meta the Kleisli `return` blocks.
  padH : 𝒱._≈_ (𝒱._⊗₁_ (𝒱.id {St f}) H) (𝒱._⊗₁_ (𝒱.id {St f}) (pureᵏ h))
  padH = refl⟩⊗⟨ eH

  padK : 𝒱._≈_ (𝒱._⊗₁_ (𝒱.id {St f}) K) (𝒱._⊗₁_ (𝒱.id {St f}) (pureᵏ k))
  padK = refl⟩⊗⟨ eK

  pt : (p : _) → _
  pt (s , x) = bindˣ (bindˣ (padH (s , x)) ⟨≈⟩ enter-pure h (step f) s x)
           ⟨≈⟩ bindᶠ λ q → padK q ⟨≈⟩ pureᴵ k q
