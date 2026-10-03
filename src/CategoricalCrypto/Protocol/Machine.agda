{-# OPTIONS --safe --without-K --guardedness #-}

-- The semantics functor: layer 1's `Protocol` as a morphism of the machine
-- layer.  An interface is a *pair* of objects and a protocol is a machine on
-- the sum of the two polarities, which is exactly a hom of the G construction:
--
--     (A⁺ , A⁻) ⇒𝒢 (B⁺ , B⁻)   is   Machine (A⁺ + B⁻) (A⁻ + B⁺)
--
-- A protocol step makes finitely many calls, which a Mealy step cannot: each
-- call is one activation, and the pending continuation is *state* (`MSt`).
--
-- An environment that answers a call it was not asked for, or queries a
-- suspended protocol, is off-protocol; `botₚ` is the honest image, being the
-- same zero-scoring divergence `dead` maps to.  This is exactly where the
-- *unit* law of `morphism` breaks: `𝒢.id` is `σ⇒`, a stateless forwarder that
-- accepts `inj₁ a⁺` at any time, whereas `morphism wireᵖ` demands a query
-- first — at `(idle tt , inj₁ a⁺)` the two steps are `botₚ` and
-- `returnₚ (tt , inj₂ a⁺)`, so neither simulates the other.  `morphism` is a
-- map of composites, not of identities.

open import Categories.Category

open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol

module CategoricalCrypto.Protocol.Machine where

private variable A B : Iface

⟦_⟧ᴵ : Iface → Category.Obj (𝒢ₚ 0ℓ)
⟦ A ⟧ᴵ = Pos A , Neg A

module _ (P : Protocol A B) where

  data MSt : Set where
    idle : St P → MSt
    wait : (Pos A → Calls A (St P × Pos B)) → MSt

  drive : Calls A (St P × Pos B) → Dₚ (MSt × (Neg A ⊎ Pos B))
  drive (ret (s , b⁺)) = returnₚ (idle s , inj₂ b⁺)
  drive (call a k)     = returnₚ (wait k , inj₁ a)
  drive (coin μ k)     = coinₚ μ >>=ₚ λ b → drive (k b)
  drive dead           = botₚ

  stepᴹ : MSt × (Pos A ⊎ Neg B) → Dₚ (MSt × (Neg A ⊎ Pos B))
  stepᴹ (idle s , inj₂ b⁻) = drive (step P s b⁻)
  stepᴹ (wait k , inj₁ a⁺) = drive (k a⁺)
  stepᴹ (idle _ , inj₁ _)  = botₚ
  stepᴹ (wait _ , inj₂ _)  = botₚ

morphism : Protocol A B → 𝒢ₚ 0ℓ [ ⟦ A ⟧ᴵ , ⟦ B ⟧ᴵ ]
morphism P = MC.mk (initˢ (MSt P) (idle (init P))) (stepᴹ P)
