{-# OPTIONS --safe --without-K --guardedness #-}

-- The reachable configurations of Blum coin-tossing over `F_com` over the
-- concrete resource, corrupted receiver, as TWO machines differing only in
-- when the honest committer's share is drawn: `eagerᶜʰ` at `goᶜ` (the hybrid's
-- order, `Receiver.Hybrid`) and `deferᶜʰ` at `shareᴬʰ` (the ideal coin's,
-- `Receiver.Machine`).  The ideal coin cannot draw at `goᶜ` — its bit would be
-- `b₁ xor b₂` at a `b₂` not yet chosen — so no state map relates the hybrid to
-- the ideal side (`docs/coin-toss.md` §5).

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

module CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Reach (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss.Hiding k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Resource k
open import CategoricalCrypto.Examples.ROCommitment.Hiding k

open Core (𝒱ₚ 0ℓ)

Cⁱʰ Cᵗʰ : Iface
Cⁱʰ = Lkᴵʰ ⊗ᴵ (Advᴵᶜʰ ⊗ᴵ Honᴵᶜʰ)
Cᵗʰ = (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ) ⊗ᴵ Honᴵᶜʰ

hashᶜʰ : {S : Set} → Tbl → (Tbl → S) → Pt → Dₚ (S × (Neg unitᴵ ⊎ Pos Cⁱʰ))
hashᶜʰ t φ = lazyₚ (λ u d → φ u , inj₂ (inj₁ (digᶠ d))) t

------------------------------------------------------------------------
-- Drawing at `goᶜ`

-- `endᴱ` keeps `b₁` because the commitment cell still holds it.
data EStʰ : Set where
  preᴱ : Tbl → EStʰ
  comᴱ : Tbl → Bool → EStʰ
  opnᴱ : Tbl → Bool → Bool → EStʰ
  endᴱ : Tbl → Bool → EStʰ

eStep : EStʰ × (Pos unitᴵ ⊎ Neg Cⁱʰ) → Dₚ (EStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ))
eStep (_ , inj₁ ())
eStep (s , inj₂ (inj₁ (relayᶠ x)))          = case s of λ where
  (preᴱ t)       → hashᶜʰ t preᴱ x
  (comᴱ t b₁)    → hashᶜʰ t (λ u → comᴱ u b₁) x
  (opnᴱ t b₁ b₂) → hashᶜʰ t (λ u → opnᴱ u b₁ b₂) x
  (endᴱ t b₁)    → hashᶜʰ t (λ u → endᴱ u b₁) x
eStep (s , inj₂ (inj₂ (inj₁ (shareᴬʰ b₂)))) = case s of λ where
  (comᴱ t b₁) → returnₚ (opnᴱ t b₁ b₂ , inj₂ (inj₁ (bitᶠ b₁)))
  _           → botₚ
eStep (s , inj₂ (inj₂ (inj₂ goᶜ)))          = case s of λ where
  (preᴱ t) → coinₚ uniform-Bool >>=ₚ λ b₁ → returnₚ (comᴱ t b₁ , inj₂ (inj₁ rcptᶠ))
  _        → botₚ
eStep (s , inj₂ (inj₂ (inj₂ getᶜ)))         = case s of λ where
  (opnᴱ t b₁ b₂) → returnₚ (endᴱ t b₁ , inj₂ (inj₂ (inj₂ (tossedᶜʰ (b₁ xor b₂)))))
  _              → botₚ

stateᴱ : State
stateᴱ = initˢ EStʰ (preᴱ [])

eagerᶜʰ′ : Proc unitᴵ Cⁱʰ
eagerᶜʰ′ = mk stateᴱ eStep

------------------------------------------------------------------------
-- …and drawing at `shareᴬʰ`

-- `endᴰ` keeps the share, which makes the relation to `eagerᶜʰ` a pointwise
-- equality rather than an existential.
data DStʰ : Set where
  preᴰ : Tbl → DStʰ
  comᴰ : Tbl → DStʰ
  opnᴰ : Tbl → Bool → Bool → DStʰ
  endᴰ : Tbl → Bool → DStʰ

dStep : DStʰ × (Pos unitᴵ ⊎ Neg Cⁱʰ) → Dₚ (DStʰ × (Neg unitᴵ ⊎ Pos Cⁱʰ))
dStep (_ , inj₁ ())
dStep (s , inj₂ (inj₁ (relayᶠ x)))          = case s of λ where
  (preᴰ t)       → hashᶜʰ t preᴰ x
  (comᴰ t)       → hashᶜʰ t comᴰ x
  (opnᴰ t b₁ b₂) → hashᶜʰ t (λ u → opnᴰ u b₁ b₂) x
  (endᴰ t b₁)    → hashᶜʰ t (λ u → endᴰ u b₁) x
dStep (s , inj₂ (inj₂ (inj₁ (shareᴬʰ b₂)))) = case s of λ where
  (comᴰ t) → coinₚ uniform-Bool >>=ₚ λ b₁ →
               returnₚ (opnᴰ t b₁ b₂ , inj₂ (inj₁ (bitᶠ b₁)))
  _        → botₚ
dStep (s , inj₂ (inj₂ (inj₂ goᶜ)))          = case s of λ where
  (preᴰ t) → returnₚ (comᴰ t , inj₂ (inj₁ rcptᶠ))
  _        → botₚ
dStep (s , inj₂ (inj₂ (inj₂ getᶜ)))         = case s of λ where
  (opnᴰ t b₁ b₂) → returnₚ (endᴰ t b₁ , inj₂ (inj₂ (inj₂ (tossedᶜʰ (b₁ xor b₂)))))
  _              → botₚ

stateᴰ : State
stateᴰ = initˢ DStʰ (preᴰ [])

deferᶜʰ′ : Proc unitᴵ Cⁱʰ
deferᶜʰ′ = mk stateᴰ dStep

------------------------------------------------------------------------
-- …at the bracket the grade is compared in

eagerᶜʰ : Proc unitᴵ Cᵗʰ
eagerᶜʰ = sandwichᴹ eagerᶜʰ′ (Sum.map₂ ⊎assocʳ) (Sum.map₂ ⊎assocˡ)

deferᶜʰ : Proc unitᴵ Cᵗʰ
deferᶜʰ = sandwichᴹ deferᶜʰ′ (Sum.map₂ ⊎assocʳ) (Sum.map₂ ⊎assocˡ)
