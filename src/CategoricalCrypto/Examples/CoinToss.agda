{-# OPTIONS --safe --without-K --guardedness #-}

-- Blum coin-tossing over `F_com`, corrupted committer: the protocol, as a
-- process OVER the commitment's honest interface.
--
-- P1 is the corrupted committer, so its whole interaction with the commitment
-- is `Examples.ROCommitment.Advᴵ` and the only thing the coin-toss protocol has
-- to run is P2: it hears the commitment's reports (`rcptᴴ`, `openedᴴ b₁`,
-- `refusedᴴ`), answers the receipt with a freshly sampled share `b₂` sent IN
-- THE CLEAR to the corrupted P1 — hence on the adversary-facing `Advᴵᶜ` — and
-- outputs `b₁ xor b₂` when the opening arrives.
--
-- The domain is `Honᴵ`, whose `Neg` is empty: P2 never talks to the
-- commitment, which is what makes this the *composable* stage — its domain is
-- the codomain of the `F_com` realization, so `UC.Asymptotic.Compose._∙ᶠ_`
-- plugs the two together (`docs/coin-toss.md`).

open import Data.Bool.Base using (Bool; _xor_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Base using (case_of_)
open import Level using (0ℓ)

open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin using (coinₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒫ₚ)
open import CategoricalCrypto.UC.Machine using (Proc)

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.CoinToss (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- Interfaces

-- P2's share, which a corrupted P1 simply reads off the network.  It carries
-- no query: the corrupted party sends P2 nothing that is not already a
-- commitment message.
data ShareA : Set where
  shareᴬ : Bool → ShareA

Advᴵᶜ : Iface
Advᴵᶜ = ShareA ⇿ ⊥

-- P2's environment-facing port: report-only, as `Honᴵ` is.
data CoinA : Set where
  tossedᶜ  : Bool → CoinA
  abortedᶜ : CoinA

Honᴵᶜ : Iface
Honᴵᶜ = CoinA ⇿ ⊥

------------------------------------------------------------------------
-- The protocol

-- Before the receipt, holding the share, and done.
data PSt : Set where
  freshᵖ : PSt
  heldᵖ  : Bool → PSt
  doneᵖ  : PSt

-- As in `Examples.ROCommitment`, the STATE is split inside each letter's
-- clause.
πStep : PSt × (Pos Honᴵ ⊎ Neg (Advᴵᶜ ⊗ᴵ Honᴵᶜ))
      → Dₚ (PSt × (Neg Honᴵ ⊎ Pos (Advᴵᶜ ⊗ᴵ Honᴵᶜ)))
πStep (s , inj₁ rcptᴴ)        = case s of λ where
  freshᵖ → coinₚ uniform-Bool >>=ₚ λ b₂ → returnₚ (heldᵖ b₂ , inj₂ (inj₁ (shareᴬ b₂)))
  _      → botₚ
πStep (s , inj₁ (openedᴴ b₁)) = case s of λ where
  (heldᵖ b₂) → returnₚ (doneᵖ , inj₂ (inj₂ (tossedᶜ (b₁ xor b₂))))
  _          → botₚ
πStep (s , inj₁ refusedᴴ)     = case s of λ where
  (heldᵖ _) → returnₚ (doneᵖ , inj₂ (inj₂ abortedᶜ))
  _         → botₚ
πStep (_ , inj₂ (inj₁ ()))
πStep (_ , inj₂ (inj₂ ()))

stateᵖ : State
stateᵖ = record { obj = PSt ; point = λ _ → returnₚ freshᵖ ; discard = λ _ → returnₚ tt }

toss : Proc Honᴵ (Advᴵᶜ ⊗ᴵ Honᴵᶜ)
toss = mk stateᵖ πStep
