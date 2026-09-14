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

open import Data.Bool.Base using (Bool; _xor_)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ)
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Base using (case_of_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin using (coinₚ)
open import ProbabilisticLogic.Dp.Reasoning
open import ProbabilisticLogic.Dp.Uniform using (uniformₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.Machine.Wire using (sandwichᴹ)

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Examples.CoinToss.Ideal.Reach (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss k
open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k

open Core (𝒱ₚ 0ℓ)

-- The grade the hybrid carries, in the two brackets the associator that
-- `UC.Asymptotic.Compose._∙ᶠ_` leaves in front of it sits between.
Cⁱ Cᵗ : Iface
Cⁱ = Lkᴵ ⊗ᴵ (Advᴵᶜ ⊗ᴵ Honᴵᶜ)
Cᵗ = (Lkᴵ ⊗ᴵ Advᴵᶜ) ⊗ᴵ Honᴵᶜ

-- The oracle table, and how far the toss has got: before the commitment,
-- holding the committed bit and the published share, and released.
data CSt : Set where
  preᶜ  : Tbl → CSt
  midᶜ  : Tbl → Bool → Bool → CSt
  postᶜ : Tbl → Bool → CSt

hashᶜ : Tbl → (Tbl → CSt) → Pt → Dₚ (CSt × (Neg unitᴵ ⊎ Pos Cⁱ))
hashᶜ t φ x = case lookupPt t x of λ where
  (just d) → returnₚ (φ t , inj₂ (inj₁ (digˢ d)))
  nothing  → uniformₚ k >>=ₚ λ h → returnₚ (φ ((x , h) ∷ t) , inj₂ (inj₁ (digˢ h)))

hashᶜ-hit : (t : Tbl) (φ : Tbl → CSt) (x : Pt) (d : Dig) → lookupPt t x ≡ just d
          → hashᶜ t φ x ≈ₚ returnₚ (φ t , inj₂ (inj₁ (digˢ d)))
hashᶜ-hit t φ x d eq rewrite eq = ≈refl

hashᶜ-miss : (t : Tbl) (φ : Tbl → CSt) (x : Pt) → lookupPt t x ≡ nothing
           → hashᶜ t φ x
             ≈ₚ (uniformₚ k >>=ₚ λ h → returnₚ (φ ((x , h) ∷ t) , inj₂ (inj₁ (digˢ h))))
hashᶜ-miss t φ x eq rewrite eq = ≈refl

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
stateᶜ = record { obj = CSt ; point = λ _ → returnₚ (preᶜ []) ; discard = λ _ → returnₚ tt }

coinᶜ′ : Proc unitᴵ Cⁱ
coinᶜ′ = mk stateᶜ cStep

-- …and at the bracket `_∙ᶠ_`'s associator leaves the grade in.
coinᶜ : Proc unitᴵ Cᵗ
coinᶜ = sandwichᴹ coinᶜ′ (Sum.map (λ a → a) ⊎assocʳ) (Sum.map (λ a → a) ⊎assocˡ)
