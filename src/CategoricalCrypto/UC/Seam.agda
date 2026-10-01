{-# OPTIONS --safe --without-K --guardedness #-}

-- A finite strategy embedded as an environment (`strategyEnv`: its state is
-- the remaining tree, an `ask` is a message on the plugged interface, a `coin`
-- is a `Dₚ` coin step).  `UC.Seam.Adequacy.adequacy` says the closed composite
-- `strategyEnv B d ∘ u` observes layer 1's own run `runᴹ u d`.
--
-- Interfaces are EXPLICIT in every definition below: an interface left
-- implicit in a `Proc` argument makes Agda invert a `Machine` type under the
-- machine tensor (the 10 GiB inversion `UC.Machine.𝒫ᴵ` records).

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base using (⊤)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.UC.Seam where

private
  module MC = Core (𝒱ₚ 0ℓ)

------------------------------------------------------------------------
-- A strategy as an environment

-- Between activations the environment is about to play the rest of its tree,
-- or suspended on the answer to a query it has issued.
data EnvSt (B : Iface) : Set where
  play : Strat (Neg B) (Pos B) → EnvSt B
  susp : (Pos B → Strat (Neg B) (Pos B)) → EnvSt B

module _ (B : Iface) where

  -- Play the tree to its next interface boundary: a query on `B`, or the
  -- verdict on the tick interface.
  playˢ : Strat (Neg B) (Pos B) → Dₚ (EnvSt B × (Neg B ⊎ Bool))
  playˢ (out b)    = returnₚ (play (out b) , inj₂ b)
  playˢ (ask q k)  = returnₚ (susp k , inj₁ q)
  playˢ (coin μ k) = coinₚ μ >>=ₚ λ b → playˢ (k b)

  -- The environment is activated by the verdict interface's tick and by the
  -- process's answers; anything else is off-protocol, hence `botₚ`.
  stepˢ : EnvSt B × (Pos B ⊎ ⊤) → Dₚ (EnvSt B × (Neg B ⊎ Bool))
  stepˢ (play d , inj₂ _) = playˢ d
  stepˢ (susp k , inj₁ p) = playˢ (k p)
  stepˢ (play _ , inj₁ _) = botₚ
  stepˢ (susp _ , inj₂ _) = botₚ

  stateˢ : Strat (Neg B) (Pos B) → MC.State
  stateˢ d = initˢ (EnvSt B) (play d)

  strategyEnv : Strat (Neg B) (Pos B) → Proc B Ωᴵ
  strategyEnv d = MC.mk (stateˢ d) stepˢ
