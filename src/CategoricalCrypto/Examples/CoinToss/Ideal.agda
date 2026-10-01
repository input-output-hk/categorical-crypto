{-# OPTIONS --safe --without-K --guardedness #-}

-- The ideal coin and the joint simulator for Blum coin-tossing over `F_com`
-- against a corrupted committer.
--
-- `Fcoin` leaks the coin before delivering it (`sampleᵏ`, then `deliverᵏ` or
-- `abortᵏ`): Blum's corrupted committer sees the honest share before deciding
-- whether to open, so the coin is unfair in Cleve's sense and a fair ideal
-- coin has no simulator (`docs/coin-toss.md` §5).
--
-- `simJ` faces both the commitment's leak port and the toss's adversary port
-- (§5 Form A rules out a tensor simulator).  It runs the random oracle itself,
-- buys the coin at `commitˢ b₁` and publishes the share `b₁ xor c`, so the
-- hybrid's output `b₁ xor share` is `Fcoin`'s `c`.

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

module CategoricalCrypto.Examples.CoinToss.Ideal (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss k
open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Resource k

open Core (𝒱ₚ 0ℓ)

------------------------------------------------------------------------
-- The simulator-facing port of the ideal coin

data CoinQ : Set where
  sampleᵏ  : CoinQ
  deliverᵏ : CoinQ
  abortᵏ   : CoinQ

data CoinR : Set where
  coinᵏ : Bool → CoinR

Lkᴵᶜ : Iface
Lkᴵᶜ = CoinR ⇿ CoinQ

------------------------------------------------------------------------
-- The ideal coin

data FSt : Set where
  freshᵏ : FSt
  heldᵏ  : Bool → FSt
  doneᵏ  : FSt

coinStep : FSt × (Pos unitᴵ ⊎ Neg (Lkᴵᶜ ⊗ᴵ Honᴵᶜ))
         → Dₚ (FSt × (Neg unitᴵ ⊎ Pos (Lkᴵᶜ ⊗ᴵ Honᴵᶜ)))
coinStep (_ , inj₁ ())
coinStep (s , inj₂ (inj₁ sampleᵏ))  = case s of λ where
  freshᵏ → coinₚ uniform-Bool >>=ₚ λ c → returnₚ (heldᵏ c , inj₂ (inj₁ (coinᵏ c)))
  _      → botₚ
coinStep (s , inj₂ (inj₁ deliverᵏ)) = case s of λ where
  (heldᵏ c) → returnₚ (doneᵏ , inj₂ (inj₂ (tossedᶜ c)))
  _         → botₚ
coinStep (s , inj₂ (inj₁ abortᵏ))   = case s of λ where
  (heldᵏ _) → returnₚ (doneᵏ , inj₂ (inj₂ abortedᶜ))
  _         → botₚ
coinStep (_ , inj₂ (inj₂ ()))

stateᵏ : State
stateᵏ = initˢ FSt freshᵏ

Fcoin : Proc unitᴵ (Lkᴵᶜ ⊗ᴵ Honᴵᶜ)
Fcoin = mk stateᵏ coinStep

------------------------------------------------------------------------
-- The joint simulator

data JSt : Set where
  preʲ : Tbl → JSt
  askʲ : Tbl → Bool → JSt
  midʲ : Tbl → JSt
  endʲ : Tbl → JSt

hashJ : Tbl → (Tbl → JSt) → Pt → Dₚ (JSt × (Neg Lkᴵᶜ ⊎ Pos (Lkᴵ ⊗ᴵ Advᴵᶜ)))
hashJ t φ = lazyₚ (λ u d → φ u , inj₂ (inj₁ (digˢ d))) t

jStep : JSt × (Pos Lkᴵᶜ ⊎ Neg (Lkᴵ ⊗ᴵ Advᴵᶜ)) → Dₚ (JSt × (Neg Lkᴵᶜ ⊎ Pos (Lkᴵ ⊗ᴵ Advᴵᶜ)))
jStep (s , inj₂ (inj₁ (hashˢ x)))    = case s of λ where
  (preʲ t)   → hashJ t preʲ x
  (askʲ t b) → hashJ t (λ u → askʲ u b) x
  (midʲ t)   → hashJ t midʲ x
  (endʲ t)   → hashJ t endʲ x
jStep (s , inj₂ (inj₁ (commitˢ b₁))) = case s of λ where
  (preʲ t) → returnₚ (askʲ t b₁ , inj₁ sampleᵏ)
  _        → botₚ
jStep (s , inj₂ (inj₁ openˢ))        = case s of λ where
  (midʲ t) → returnₚ (endʲ t , inj₁ deliverᵏ)
  _        → botₚ
jStep (s , inj₂ (inj₁ failˢ))        = case s of λ where
  (midʲ t) → returnₚ (endʲ t , inj₁ abortᵏ)
  _        → botₚ
jStep (s , inj₁ (coinᵏ c))           = case s of λ where
  (askʲ t b₁) → returnₚ (midʲ t , inj₂ (inj₂ (shareᴬ (b₁ xor c))))
  _           → botₚ
jStep (_ , inj₂ (inj₂ ()))

stateʲ : State
stateʲ = initˢ JSt (preʲ [])

simJ : Proc Lkᴵᶜ (Lkᴵ ⊗ᴵ Advᴵᶜ)
simJ = mk stateʲ jStep
