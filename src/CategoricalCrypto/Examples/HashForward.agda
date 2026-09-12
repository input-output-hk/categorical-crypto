{-# OPTIONS --safe --without-K --guardedness #-}

-- Hash-then-forward: the toy whose simulator has an inhabited interface and
-- spends a query, at an explicitly NONTRIVIAL grade.
--
-- A leaky channel and a hash oracle sit below, as one resource `Resᴵ`.  The
-- IDEAL functionality is that resource with its leak exposed on the
-- simulator-facing port `Lkᴵ`; the REAL protocol hardens it, answering the
-- adversary's single query `peekᴬ` with the DIGEST of the leaked message
-- instead of the message.  The simulator is what makes the two agree: given the
-- ideal's view it fetches the leak and hashes it, so its own run is two queries
-- on `Lkᴵ`, exactly one of them a hash query.
--
-- The agreement is EXACT — one machine equality, no error term — which is the
-- point: the example exists for the types and the grading, not for a
-- probabilistic argument.  Nothing is assumed about the resource, so the
-- statement holds for whatever the closure plugs in below; the emulation is
-- the "real is at least as secure as ideal" direction, and the toy makes no
-- claim that hashing makes it strictly more so.
--
-- `docs/hash-forward.md` records why the oracle sits below rather than inside
-- either system, and what the alternatives cost.

open import Categories.Category using (Category; _[_≈_])

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Base using (case_of_)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒢ₚ; 𝒫ₚ)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; subᴵ′; wireᴹ)
open import CategoricalCrypto.UC.Machine.Wire using (sandwichᴹ; ∘-wireᴹ)

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.HashForward (Msg Dig : Set) where

private
  module 𝒫 = Category 𝒫ᴵ

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- Interfaces

-- The resource below: a channel that stores one message, delivers it and leaks
-- it, and a hash oracle.  Both worlds call down into it.
data ResQ : Set where
  putᴿ  : Msg → ResQ
  getᴿ  : ResQ
  leakᴿ : ResQ
  hashᴿ : Msg → ResQ

data ResA : Set where
  ackᴿ : ResA
  gotᴿ : Msg → ResA
  lkᴿ  : Msg → ResA
  digᴿ : Dig → ResA

Resᴵ : Iface
Resᴵ = ResA ⇿ ResQ

-- The honest interface, common to both worlds.
data HonQ : Set where
  sendᴴ : Msg → HonQ
  recvᴴ : HonQ

data HonA : Set where
  ackᴴ : HonA
  msgᴴ : Msg → HonA

Honᴵ : Iface
Honᴵ = HonA ⇿ HonQ

-- The REAL adversary-facing port: one query, answered with a digest.
data AdvQ : Set where
  peekᴬ : AdvQ

data AdvA : Set where
  wireᴬ : Dig → AdvA

Advᴵ : Iface
Advᴵ = AdvA ⇿ AdvQ

-- The IDEAL simulator-facing port: the leak, and the oracle relayed.
data LkQ : Set where
  leakˢ : LkQ
  hashˢ : Msg → LkQ

data LkA : Set where
  lkˢ  : Msg → LkA
  digˢ : Dig → LkA

Lkᴵ : Iface
Lkᴵ = LkA ⇿ LkQ

------------------------------------------------------------------------
-- The ideal functionality

-- It is a WIRE: the resource's own ports, relabelled onto the simulator's and
-- the honest one.  Statelessness is what keeps the simulated composite free of
-- the ⊕-trace (`UC.Machine.Wire`), and it is honest — the channel's state is
-- the resource's, not the functionality's.
downᶠ : Neg (Lkᴵ ⊗ᴵ Honᴵ) → Neg Resᴵ
downᶠ (inj₁ leakˢ)     = leakᴿ
downᶠ (inj₁ (hashˢ m)) = hashᴿ m
downᶠ (inj₂ (sendᴴ m)) = putᴿ m
downᶠ (inj₂ recvᴴ)     = getᴿ

upᶠ : Pos Resᴵ → Pos (Lkᴵ ⊗ᴵ Honᴵ)
upᶠ ackᴿ     = inj₂ ackᴴ
upᶠ (gotᴿ m) = inj₂ (msgᴴ m)
upᶠ (lkᴿ m)  = inj₁ (lkˢ m)
upᶠ (digᴿ d) = inj₁ (digˢ d)

ideal : Proc Resᴵ (Lkᴵ ⊗ᴵ Honᴵ)
ideal = wireᴹ upᶠ downᶠ

------------------------------------------------------------------------
-- The simulator

-- Three states, because answering one `peekᴬ` takes two queries: fetch the
-- leak, then hash it.  `botₚ` is the honest image of an off-protocol
-- activation, as in `Protocol.Machine.stepᴹ`.
data SSt : Set where
  idleˢ  : SSt
  awaitL : SSt
  awaitD : SSt

simStep : SSt × (Pos Lkᴵ ⊎ Neg Advᴵ) → Dₚ (SSt × (Neg Lkᴵ ⊎ Pos Advᴵ))
simStep (idleˢ  , inj₂ peekᴬ)    = returnₚ (awaitL , inj₁ leakˢ)
simStep (awaitL , inj₁ (lkˢ m))  = returnₚ (awaitD , inj₁ (hashˢ m))
simStep (awaitD , inj₁ (digˢ d)) = returnₚ (idleˢ  , inj₂ (wireᴬ d))
simStep _                        = botₚ

stateˢ : State
stateˢ = record { obj = SSt ; point = λ _ → returnₚ idleˢ ; discard = λ _ → returnₚ tt }

simulator : Proc Lkᴵ Advᴵ
simulator = mk stateˢ simStep

------------------------------------------------------------------------
-- The real protocol

-- The simulator's own program, run against the resource instead of against the
-- ideal functionality: `peekᴬ` fetches the channel's leak and hashes it, and
-- honest traffic is relayed.  This is the step table a reader would write for
-- "hash what is on the wire"; that it is also the simulated composite's is
-- `real-factors`.
-- The state is split INSIDE each letter's clause, never across them: a clause
-- with a constructor in the state position would make the relayed cases stick
-- at a variable state, and `real-factors` compares them there.
realStep : SSt × (Pos Resᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ))
         → Dₚ (SSt × (Neg Resᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)))
realStep (s , inj₁ ackᴿ)             = returnₚ (s , inj₂ (inj₂ ackᴴ))
realStep (s , inj₁ (gotᴿ m))         = returnₚ (s , inj₂ (inj₂ (msgᴴ m)))
realStep (s , inj₁ (lkᴿ m))          = case s of λ where
  awaitL → returnₚ (awaitD , inj₁ (hashᴿ m))
  _      → botₚ
realStep (s , inj₁ (digᴿ d))         = case s of λ where
  awaitD → returnₚ (idleˢ , inj₂ (inj₁ (wireᴬ d)))
  _      → botₚ
realStep (s , inj₂ (inj₁ peekᴬ))     = case s of λ where
  idleˢ → returnₚ (awaitL , inj₁ leakᴿ)
  _     → botₚ
realStep (s , inj₂ (inj₂ (sendᴴ m))) = returnₚ (s , inj₁ (putᴿ m))
realStep (s , inj₂ (inj₂ recvᴴ))     = returnₚ (s , inj₁ getᴿ)

real : Proc Resᴵ (Advᴵ ⊗ᴵ Honᴵ)
real = mk stateˢ realStep

------------------------------------------------------------------------
-- The factoring

private
  map-ret : {A B : Set} (h : A → B) (x : A) → mapₚ h (returnₚ x) ≈ₚ returnₚ (h x)
  map-ret h x = >>=ₚ-identityˡ x _

  map-bot : {A B : Set} (h : A → B) → mapₚ h (botₚ {A = A}) ≈ₚ botₚ
  map-bot h = bot-bind-≈ₚ _

  -- The two shapes a relayed step takes: the simulator answers, or it is
  -- off-protocol and the relay carries the divergence through.
  relayed : {A B C : Set} (g : A → B) (h : B → C) (x : A)
          → returnₚ (h (g x)) ≈ₚ mapₚ h (mapₚ g (returnₚ x))
  relayed g h x = ≈sym (bindˣ (map-ret g x) ⟨≈⟩ map-ret h (g x))

  dead : {A B C : Set} (g : A → B) (h : B → C) → botₚ ≈ₚ mapₚ h (mapₚ g (botₚ {A = A}))
  dead g h = ≈sym (bindˣ (map-bot g) ⟨≈⟩ map-bot h)

-- The real protocol IS the simulator standing in front of the ideal
-- functionality.  A wire below costs no trace (`∘-wireᴹ`), so the composite is
-- the relay `subᴵ simulator` with its interface renamed — same state — and the
-- equality is one pointwise case analysis.
real-factors : 𝒫._≈_ {Resᴵ} {Advᴵ ⊗ᴵ Honᴵ} real
                 (𝒫._∘_ (subᴵ′ {Lkᴵ} {Advᴵ} {Honᴵ} simulator) ideal)
real-factors = ≲⇒≈ᴹ (mk-cong pt) ○ᴹ ⟺ᴹ (∘-wireᴹ upᶠ downᶠ (subᴵ′ simulator))
  where
  pt : (p : _) → _
  pt (s      , inj₁ ackᴿ)             = ≈sym (map-ret _ _)
  pt (s      , inj₁ (gotᴿ m))         = ≈sym (map-ret _ _)
  pt (idleˢ  , inj₁ (lkᴿ m))          = dead _ _
  pt (awaitL , inj₁ (lkᴿ m))          = relayed _ _ _
  pt (awaitD , inj₁ (lkᴿ m))          = dead _ _
  pt (idleˢ  , inj₁ (digᴿ d))         = dead _ _
  pt (awaitL , inj₁ (digᴿ d))         = dead _ _
  pt (awaitD , inj₁ (digᴿ d))         = relayed _ _ _
  pt (idleˢ  , inj₂ (inj₁ peekᴬ))     = relayed _ _ _
  pt (awaitL , inj₂ (inj₁ peekᴬ))     = dead _ _
  pt (awaitD , inj₂ (inj₁ peekᴬ))     = dead _ _
  pt (s      , inj₂ (inj₂ (sendᴴ m))) = ≈sym (map-ret _ _)
  pt (s      , inj₂ (inj₂ recvᴴ))     = ≈sym (map-ret _ _)
