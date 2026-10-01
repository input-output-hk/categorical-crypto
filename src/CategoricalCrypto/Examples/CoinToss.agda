{-# OPTIONS --safe --without-K --guardedness #-}

-- Blum coin-tossing over `F_com`, corrupted committer (P1): P2's side, as a
-- process over the commitment's honest interface `Honᴵ`.  P2 answers the
-- receipt with a fresh share `b₂`, sent in the clear on `Advᴵᶜ`, and outputs
-- `b₁ xor b₂` at the opening.  Its domain `Honᴵ` has an empty `Neg` (P2 never
-- talks to the commitment) and is the codomain of the `F_com` realization, so
-- `_∙ᶠ_` plugs the two together (`docs/coin-toss.md`).

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

module CategoricalCrypto.Examples.CoinToss (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- Interfaces

-- No query: a corrupted P1 sends P2 nothing that is not already a commitment
-- message.
data ShareA : Set where
  shareᴬ : Bool → ShareA

Advᴵᶜ : Iface
Advᴵᶜ = ShareA ⇿ ⊥

data CoinA : Set where
  tossedᶜ  : Bool → CoinA
  abortedᶜ : CoinA

Honᴵᶜ : Iface
Honᴵᶜ = CoinA ⇿ ⊥

------------------------------------------------------------------------
-- The protocol

data PSt : Set where
  freshᵖ : PSt
  heldᵖ  : Bool → PSt
  doneᵖ  : PSt

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
stateᵖ = initˢ PSt freshᵖ

toss : Proc Honᴵ (Advᴵᶜ ⊗ᴵ Honᴵᶜ)
toss = mk stateᵖ πStep
