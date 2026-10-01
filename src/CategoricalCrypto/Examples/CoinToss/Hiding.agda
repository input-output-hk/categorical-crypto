{-# OPTIONS --safe --without-K --guardedness #-}

-- Blum coin-tossing over `F_com`, corrupted receiver (P2): P1's side, as a
-- process over the commitment's hiding honest interface.  Started by the
-- environment, it samples and commits to `b₁`, hears `b₂` in the clear, opens,
-- and outputs `b₁ xor b₂`.  `Neg Honᴵʰ` is inhabited (`commitᴱ`, `openᴱ`), so
-- unlike `Examples.CoinToss` this stage makes downward calls.

open import Data.Bool.Base
open import Data.Empty
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Function.Base
open import Level

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.CoinToss.Hiding (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment.Hiding k

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- Interfaces

data ShareQ : Set where
  shareᴬʰ : Bool → ShareQ

Advᴵᶜʰ : Iface
Advᴵᶜʰ = ⊥ ⇿ ShareQ

data CoinQʰ : Set where
  goᶜ  : CoinQʰ
  getᶜ : CoinQʰ

data CoinAʰ : Set where
  tossedᶜʰ  : Bool → CoinAʰ
  abortedᶜʰ : CoinAʰ

Honᴵᶜʰ : Iface
Honᴵᶜʰ = CoinAʰ ⇿ CoinQʰ

------------------------------------------------------------------------
-- The protocol

data QSt : Set where
  freshᵗ : QSt
  comᵗ   : Bool → QSt
  openᵗ  : Bool → Bool → QSt
  doneᵗ  : QSt

τStep : QSt × (Pos Honᴵʰ ⊎ Neg (Advᴵᶜʰ ⊗ᴵ Honᴵᶜʰ))
      → Dₚ (QSt × (Neg Honᴵʰ ⊎ Pos (Advᴵᶜʰ ⊗ᴵ Honᴵᶜʰ)))
τStep (s , inj₁ nakᴱ)                 = case s of λ where
  (comᵗ _)    → returnₚ (doneᵗ , inj₂ (inj₂ abortedᶜʰ))
  (openᵗ _ _) → returnₚ (doneᵗ , inj₂ (inj₂ abortedᶜʰ))
  _           → botₚ
τStep (s , inj₂ (inj₁ (shareᴬʰ b₂)))  = case s of λ where
  (comᵗ b₁) → returnₚ (openᵗ b₁ b₂ , inj₁ openᴱ)
  _         → botₚ
τStep (s , inj₂ (inj₂ goᶜ))           = case s of λ where
  freshᵗ → coinₚ uniform-Bool >>=ₚ λ b₁ → returnₚ (comᵗ b₁ , inj₁ (commitᴱ b₁))
  _      → botₚ
τStep (s , inj₂ (inj₂ getᶜ))          = case s of λ where
  (openᵗ b₁ b₂) → returnₚ (doneᵗ , inj₂ (inj₂ (tossedᶜʰ (b₁ xor b₂))))
  _             → botₚ

stateᵗ : State
stateᵗ = initˢ QSt freshᵗ

tossʰ : Proc Honᴵʰ (Advᴵᶜʰ ⊗ᴵ Honᴵᶜʰ)
tossʰ = mk stateᵗ τStep
