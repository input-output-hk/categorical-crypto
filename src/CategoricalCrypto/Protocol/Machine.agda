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

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Strategy

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Protocol.Machine where

private
  module MC = Core (𝒱ₚ 0ℓ)

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

  stateᴹ : MC.State
  stateᴹ = record { obj = MSt ; point = λ _ → returnₚ (idle (init P)) }

morphism : Protocol A B → 𝒢ₚ 0ℓ [ ⟦ A ⟧ᴵ , ⟦ B ⟧ᴵ ]
morphism P = MC.mk (stateᴹ P) (stepᴹ P)

------------------------------------------------------------------------
-- The closed-machine run

-- The shape of a closed protocol's image, both polarities of `unitᴵ` being
-- empty; `runᴹ` runs a strategy against any machine of it.  The initial state
-- is `point`, which at a Kleisli base is itself effectful.
Closed : Iface → Set₁
Closed B = MC.Machine (⊥ ⊎ Neg B) (⊥ ⊎ Pos B)

module _ (M : Closed B) where

  -- Named rather than `where`-local so that a lemma about a run can quantify
  -- over it (`UC.Machine.Run.resume-ϕ`).
  resumeᴹ : (MC.St M → Pos B → Dₚ Bool) → MC.St M × (⊥ ⊎ Pos B) → Dₚ Bool
  resumeᴹ c (_  , inj₁ a) = ⊥-elim a
  resumeᴹ c (m′ , inj₂ r) = c m′ r

  runᴹFrom : MC.St M → Strat (Neg B) (Pos B) → Dₚ Bool
  runᴹFrom m (out b)    = returnₚ b
  runᴹFrom m (coin μ k) = coinₚ μ >>=ₚ λ b → runᴹFrom m (k b)
  runᴹFrom m (ask q k)  =
    MC.step M (m , inj₂ q) >>=ₚ resumeᴹ λ m′ r → runᴹFrom m′ (k r)

  runᴹ : Strat (Neg B) (Pos B) → Dₚ Bool
  runᴹ d = MC.point (MC.state M) tt >>=ₚ λ m → runᴹFrom m d
