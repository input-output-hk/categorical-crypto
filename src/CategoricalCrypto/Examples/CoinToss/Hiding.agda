{-# OPTIONS --safe --without-K --guardedness #-}

-- Blum coin-tossing over `F_com`, corrupted receiver: the protocol, as a
-- process over the commitment's HIDING honest interface.
--
-- The two corruption cases need `F_com` at genuinely different ports
-- (`docs/fcom-hiding.md`), so they are two protocols and two composed
-- theorems.  Here P1 is honest, so the coin-toss stage is P1's side: the
-- environment starts it, it samples its share `b₁` and commits to it, the
-- corrupted P2 sends its share `b₂` in the clear, it opens, and it outputs
-- `b₁ xor b₂`.
--
-- Unlike the extraction half the domain's `Neg` is INHABITED — `commitᴱ` and
-- `openᴱ` are how an honest committer drives `F_com` — so this stage does make
-- downward calls, one per activation from above, and its certificate is at
-- rate 1 rather than 0.

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

module CategoricalCrypto.Examples.CoinToss.Hiding (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment.Hiding k
  using (Honᴵʰ; commitᴱ; openᴱ; nakᴱ)

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- Interfaces

-- The corrupted receiver's share, which it sends to the honest committer.  It
-- is a QUERY here, where the extraction half's `shareᴬ` was an answer: the
-- corrupt party is the one that speaks.
data ShareQ : Set where
  shareᴬʰ : Bool → ShareQ

Advᴵᶜʰ : Iface
Advᴵᶜʰ = ⊥ ⇿ ShareQ

-- P1's environment-facing port: start, and collect.
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
stateᵗ = record { obj = QSt ; point = λ _ → returnₚ freshᵗ ; discard = λ _ → returnₚ tt }

tossʰ : Proc Honᴵʰ (Advᴵᶜʰ ⊗ᴵ Honᴵᶜʰ)
tossʰ = mk stateᵗ τStep
