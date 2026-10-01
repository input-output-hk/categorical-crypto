{-# OPTIONS --safe --without-K --guardedness #-}

-- The ideal coin and the joint simulator for Blum coin-tossing over `F_com`
-- against a corrupted receiver.
--
-- `Fcoinʰ` leaks before it delivers, as `Fcoin` does (`Examples.CoinToss.Ideal`):
-- `startᵏʰ` when the honest committer is started, then `coinᵏʰ c` when the
-- simulator buys the bit, which is the functionality's own uniform draw.  It
-- has no abort because the composite has none: `F_com`'s refusal `nakᴱ`
-- reaches the stage only through `rejᴿ`, which
-- `Examples.ROCommitment.Hiding.downᶠʰ` never asks for.
--
-- `simJʰ` (`docs/coin-toss.md` §5 Form B) runs the random oracle itself,
-- publishes the receipt, and at the receiver's share `b₂` buys the coin and
-- reports the committed bit as `bitᶠ (c xor b₂)`, so the hybrid's `b₁ xor b₂`
-- is `Fcoinʰ`'s `c`.

open import Data.Bool.Base
open import Data.List.Base
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

module CategoricalCrypto.Examples.CoinToss.Ideal.Receiver (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss.Hiding k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Resource k
open import CategoricalCrypto.Examples.ROCommitment.Hiding k

open Core (𝒱ₚ 0ℓ)

------------------------------------------------------------------------
-- The simulator-facing port of the ideal coin

data LeakQʰ : Set where
  sampleᵏʰ : LeakQʰ

data LeakRʰ : Set where
  startᵏʰ : LeakRʰ
  coinᵏʰ  : Bool → LeakRʰ

Lkᴵᶜʰ : Iface
Lkᴵᶜʰ = LeakRʰ ⇿ LeakQʰ

------------------------------------------------------------------------
-- The ideal coin

data FStʰ : Set where
  freshᵏʰ : FStʰ
  waitᵏʰ  : FStʰ
  heldᵏʰ  : Bool → FStʰ
  doneᵏʰ  : FStʰ

coinStepʰ : FStʰ × (Pos unitᴵ ⊎ Neg (Lkᴵᶜʰ ⊗ᴵ Honᴵᶜʰ))
          → Dₚ (FStʰ × (Neg unitᴵ ⊎ Pos (Lkᴵᶜʰ ⊗ᴵ Honᴵᶜʰ)))
coinStepʰ (_ , inj₁ ())
coinStepʰ (s , inj₂ (inj₁ sampleᵏʰ)) = case s of λ where
  waitᵏʰ → coinₚ uniform-Bool >>=ₚ λ c → returnₚ (heldᵏʰ c , inj₂ (inj₁ (coinᵏʰ c)))
  _      → botₚ
coinStepʰ (s , inj₂ (inj₂ goᶜ))      = case s of λ where
  freshᵏʰ → returnₚ (waitᵏʰ , inj₂ (inj₁ startᵏʰ))
  _       → botₚ
coinStepʰ (s , inj₂ (inj₂ getᶜ))     = case s of λ where
  (heldᵏʰ c) → returnₚ (doneᵏʰ , inj₂ (inj₂ (tossedᶜʰ c)))
  _          → botₚ

stateᵏʰ : State
stateᵏʰ = initˢ FStʰ freshᵏʰ

Fcoinʰ : Proc unitᴵ (Lkᴵᶜʰ ⊗ᴵ Honᴵᶜʰ)
Fcoinʰ = mk stateᵏʰ coinStepʰ

------------------------------------------------------------------------
-- The joint simulator

data JStʰ : Set where
  preʲʰ : Tbl → JStʰ
  midʲʰ : Tbl → JStʰ
  askʲʰ : Tbl → Bool → JStʰ
  endʲʰ : Tbl → JStʰ

hashJʰ : Tbl → (Tbl → JStʰ) → Pt → Dₚ (JStʰ × (Neg Lkᴵᶜʰ ⊎ Pos (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ)))
hashJʰ t φ = lazyₚ (λ u d → φ u , inj₂ (inj₁ (digᶠ d))) t

jStepʰ : JStʰ × (Pos Lkᴵᶜʰ ⊎ Neg (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ))
       → Dₚ (JStʰ × (Neg Lkᴵᶜʰ ⊎ Pos (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ)))
jStepʰ (s , inj₂ (inj₁ (relayᶠ x)))   = case s of λ where
  (preʲʰ t)    → hashJʰ t preʲʰ x
  (midʲʰ t)    → hashJʰ t midʲʰ x
  (askʲʰ t b₂) → hashJʰ t (λ u → askʲʰ u b₂) x
  (endʲʰ t)    → hashJʰ t endʲʰ x
jStepʰ (s , inj₂ (inj₂ (shareᴬʰ b₂))) = case s of λ where
  (midʲʰ t) → returnₚ (askʲʰ t b₂ , inj₁ sampleᵏʰ)
  _         → botₚ
jStepʰ (s , inj₁ startᵏʰ)             = case s of λ where
  (preʲʰ t) → returnₚ (midʲʰ t , inj₂ (inj₁ rcptᶠ))
  _         → botₚ
jStepʰ (s , inj₁ (coinᵏʰ c))          = case s of λ where
  (askʲʰ t b₂) → returnₚ (endʲʰ t , inj₂ (inj₁ (bitᶠ (c xor b₂))))
  _            → botₚ

stateʲʰ : State
stateʲʰ = initˢ JStʰ (preʲʰ [])

simJʰ : Proc Lkᴵᶜʰ (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ)
simJʰ = mk stateʲʰ jStepʰ
