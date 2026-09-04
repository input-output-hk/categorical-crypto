{-# OPTIONS --safe --without-K --guardedness #-}

-- The semantics functor: layer 1's `Protocol` as a morphism of the machine
-- layer.  An interface is a *pair* of objects and a protocol is a machine on
-- the sum of the two polarities, which is exactly a hom of the G construction:
--
--     (A⁺ , A⁻) ⇒𝒢 (B⁺ , B⁻)   is   Machine (A⁺ + B⁻) (A⁻ + B⁺)
--
-- so `morphism P` needs no coercion — `⟦_⟧ᴵ` lands on `𝒢ₚ`'s objects and
-- `morphism` on its homs.
--
-- A protocol step makes finitely many calls, which a Mealy step cannot: each
-- call is one activation, and the pending continuation is *state*.  That is
-- `MSt`: idle at a protocol state, or suspended on `Pos A`.  Driving a call
-- tree to its next boundary (`drive`) is structural recursion on `Calls` — the
-- tree is inductive, so no iteration and no clock appears here either; `coin`
-- becomes a biased-coin step (`coinₚ`) and `dead` becomes divergence, whose
-- mass `cum` never counts.
--
-- An environment that answers a call it was not asked for, or queries a
-- suspended protocol, is off-protocol; `botₚ` is the honest image, being the
-- same zero-scoring divergence `dead` maps to.  This is exactly where the
-- *unit* law of `morphism` breaks: `𝒢.id` is `σ⇒`, a stateless forwarder that
-- accepts `inj₁ a⁺` at any time, whereas `morphism wireᵖ` demands a query
-- first — at `(idle tt , inj₁ a⁺)` the two steps are `botₚ` and
-- `returnₚ (tt , inj₂ a⁺)`, so neither simulates the other.  `morphism` is a
-- map of composites, not of identities; `wireᵖ` is the *sequential* wire.

open import Categories.Category using (Category; _[_,_]; _[_≈_])

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin using (coinₚ)
open import ProbabilisticLogic.Distribution.Uniform using (bool→ℚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒢ₚ)
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe using (Pr)
open import CategoricalCrypto.Strategy

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Protocol.Machine where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module 𝒢 = Category (𝒢ₚ 0ℓ)

private variable A B : Iface

-- An interface is a pair of objects, positive polarity first.
⟦_⟧ᴵ : Iface → 𝒢.Obj
⟦ A ⟧ᴵ = Pos A , Neg A

module _ {A B : Iface} (P : Protocol A B) where

  -- Between activations a protocol is either idle or holding the continuation
  -- of a call it has made.
  data MSt : Set where
    idle : St P → MSt
    wait : (Pos A → Calls A (St P × Pos B)) → MSt

  -- Run a call tree to its next interface boundary: an answer on `B`, or a
  -- call on `A` with the rest of the tree parked in the state.
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
  stateᴹ = record
    { obj     = MSt
    ; point   = λ _ → returnₚ (idle (init P))
    ; discard = λ _ → returnₚ tt
    }

morphism : Protocol A B → 𝒢ₚ 0ℓ [ ⟦ A ⟧ᴵ , ⟦ B ⟧ᴵ ]
morphism P = MC.mk (stateᴹ P) (stepᴹ P)

------------------------------------------------------------------------
-- What the agreement theorems say

-- Functoriality: `_∘ᵖ_` grafts two call trees; `𝒢`'s composition traces the
-- tensor of the two machines.  Stated, not proved — see below for the price.
Morphism-∘ : Set₁
Morphism-∘ = {A B C : Iface} (P₂ : Protocol B C) (P₁ : Protocol A B)
           → 𝒢ₚ 0ℓ [ morphism (P₂ ∘ᵖ P₁) ≈ morphism P₂ 𝒢.∘ morphism P₁ ]

-- The closed-machine run, against any machine of the shape a closed protocol's
-- image has: a strategy's ask goes in on the right summand and an answer can
-- only come back on the right one, `Pos unitᴵ` being empty.  The initial state
-- is `point`, which at a Kleisli base is itself effectful.
module _ {B : Iface} (M : MC.Machine (⊥ ⊎ Neg B) (⊥ ⊎ Pos B)) where

  -- What the strategy does with the answer.  A named continuation rather than a
  -- `where`-local one, so that a lemma about a run can quantify over it: the
  -- domain summand is empty, so the only reachable case is the strategy's own.
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

-- The interaction is finite — the strategy tree bounds it and every call tree
-- is inductive — so past some depth the coin tree's cumulative mass is
-- *exactly* layer 1's verdict probability.  `Dₚ`'s probability is a supremum,
-- which the layer never forms; a budget and a value is the `cum`-level
-- statement of the same thing.  `Machine.Pin` computes both sides at one
-- instance.
PrAgree : Set₁
PrAgree = {B : Iface} (P : Protocol unitᴵ B) (d : Strat (Neg B) (Pos B))
        → Σ[ n ∈ ℕ ] ((m : ℕ) → cum (n + m) (runᴹ (morphism P) d) bool→ℚ ≡ Pr P d)
