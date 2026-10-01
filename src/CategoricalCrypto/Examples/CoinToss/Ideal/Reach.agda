{-# OPTIONS --safe --without-K --guardedness #-}

-- The reachable configurations of Blum coin-tossing over `F_com` over the
-- concrete resource, as a machine in their own right.
--
-- Both sides of the second hop (`Examples.CoinToss.Ideal.Machine`) are
-- ⊕-traces, and their loop objects differ — `Lkᴵ ⊗ᴵ Honᴵ` against
-- `Lkᴵᶜ ⊗ᴵ Honᴵᶜ` — so no simulation runs between them.  `coinᶜ` is the third
-- machine both simulate out of, which is all an `EqClosure` needs; that is
-- `Protocol.Machine.Compose`'s `machineᶜ` method.
--
-- A third machine is not a convenience.  `(heldᵖ b₂ , (t , nothing))` — the
-- stage holding a share over an empty cell — is unreachable, but a total state
-- map has to place it, and it refuses `openˢ` while answering `failˢ` with
-- `abortedᶜ`, which no state of the ideal side does.  `coinᶜ` drops it.

open import Data.Bool.Base
open import Data.List.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base as Sum
open import Data.Sum.Base using () renaming (assocˡ to ⊎assocˡ; assocʳ to ⊎assocʳ)
open import Data.Unit.Polymorphic.Base
open import Function.Base
open import Level

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Sandwich
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Examples.CoinToss.Ideal.Reach (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss k
open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Resource k

open Core (𝒱ₚ 0ℓ)

-- The grade the hybrid carries, in the two brackets the associator that
-- `UC.Model.Family.Contextual.Compose._∙ᶠ_` leaves in front of it sits
-- between.
Cⁱ Cᵗ : Iface
Cⁱ = Lkᴵ ⊗ᴵ (Advᴵᶜ ⊗ᴵ Honᴵᶜ)
Cᵗ = (Lkᴵ ⊗ᴵ Advᴵᶜ) ⊗ᴵ Honᴵᶜ

data CSt : Set where
  preᶜ  : Tbl → CSt
  midᶜ  : Tbl → Bool → Bool → CSt
  postᶜ : Tbl → Bool → CSt

hashᶜ : Tbl → (Tbl → CSt) → Pt → Dₚ (CSt × (Neg unitᴵ ⊎ Pos Cⁱ))
hashᶜ t φ = lazyₚ (λ u d → φ u , inj₂ (inj₁ (digˢ d))) t

cStep : CSt × (Pos unitᴵ ⊎ Neg Cⁱ) → Dₚ (CSt × (Neg unitᴵ ⊎ Pos Cⁱ))
cStep (_ , inj₁ ())
cStep (s , inj₂ (inj₁ (hashˢ x)))    = case s of λ where
  (preᶜ t)       → hashᶜ t preᶜ x
  (midᶜ t b₁ b₂) → hashᶜ t (λ u → midᶜ u b₁ b₂) x
  (postᶜ t b₁)   → hashᶜ t (λ u → postᶜ u b₁) x
cStep (s , inj₂ (inj₁ (commitˢ b₁))) = case s of λ where
  (preᶜ t) → coinₚ uniform-Bool >>=ₚ λ b₂ →
               returnₚ (midᶜ t b₁ b₂ , inj₂ (inj₂ (inj₁ (shareᴬ b₂))))
  _        → botₚ
cStep (s , inj₂ (inj₁ openˢ))        = case s of λ where
  (midᶜ t b₁ b₂) → returnₚ (postᶜ t b₁ , inj₂ (inj₂ (inj₂ (tossedᶜ (b₁ xor b₂)))))
  _              → botₚ
cStep (s , inj₂ (inj₁ failˢ))        = case s of λ where
  (midᶜ t b₁ _) → returnₚ (postᶜ t b₁ , inj₂ (inj₂ (inj₂ abortedᶜ)))
  _             → botₚ
cStep (_ , inj₂ (inj₂ (inj₁ ())))
cStep (_ , inj₂ (inj₂ (inj₂ ())))

stateᶜ : State
stateᶜ = initˢ CSt (preᶜ [])

coinᶜ′ : Proc unitᴵ Cⁱ
coinᶜ′ = mk stateᶜ cStep

coinᶜ : Proc unitᴵ Cᵗ
coinᶜ = sandwichᴹ coinᶜ′ (Sum.map₂ ⊎assocʳ) (Sum.map₂ ⊎assocˡ)
