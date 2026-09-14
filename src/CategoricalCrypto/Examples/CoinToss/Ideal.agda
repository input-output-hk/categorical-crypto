{-# OPTIONS --safe --without-K --guardedness #-}

-- The ideal coin functionality, and the joint simulator for Blum coin-tossing
-- over `F_com` against a corrupted committer.
--
-- `Fcoin` LEAKS the coin before it delivers it: `sampleᵏ` draws the bit once
-- and hands it to the simulator, `deliverᵏ` releases it to the honest party
-- and `abortᵏ` refuses.  The leak is the statement's content, not a weakness
-- of it — Blum's corrupted committer sees the honest share before it decides
-- whether to open, so the coin is unfair in Cleve's sense and a FAIR ideal
-- coin has no simulator at all (`docs/coin-toss.md` §5).  Off-protocol
-- activations — a second `sampleᵏ`, a `deliverᵏ` before one — are `botₚ`, the
-- layer's image of "no behaviour", exactly as `Examples.ROCommitment.Resource`
-- has them.
--
-- `simJ` is joint in the sense §5 Form A rules out for a tensor simulator: one
-- machine facing BOTH the commitment's leak port and the coin toss's own
-- adversary port.  It runs the random oracle itself — the table is its state,
-- nothing sits below it but `Fcoin` — buys the coin at `commitˢ b₁` and
-- publishes the share `b₁ xor c`, which is what makes the hybrid's output
-- `b₁ xor share` land on `Fcoin`'s bit `c`.

open import Data.Bool.Base using (Bool; _xor_)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Base using (case_of_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin using (coinₚ)
open import ProbabilisticLogic.Dp.Uniform using (uniformₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.UC.Machine using (Proc)

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Examples.CoinToss.Ideal (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss k
open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k

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

-- Undrawn, drawn and held, released.
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
stateᵏ = record { obj = FSt ; point = λ _ → returnₚ freshᵏ ; discard = λ _ → returnₚ tt }

Fcoin : Proc unitᴵ (Lkᴵᶜ ⊗ᴵ Honᴵᶜ)
Fcoin = mk stateᵏ coinStep

------------------------------------------------------------------------
-- The joint simulator

-- Its state is the oracle table it answers from, plus how far the commitment
-- has got: nothing yet, `sampleᵏ` outstanding with the committed bit kept, the
-- share published, done.
data JSt : Set where
  preʲ : Tbl → JSt
  askʲ : Tbl → Bool → JSt
  midʲ : Tbl → JSt
  endʲ : Tbl → JSt

-- `Examples.ROCommitment.Resource`'s `hashᴿ` clause with the table in the
-- simulator's own state: a point already answered is answered again from it, a
-- fresh one draws `uniformₚ k` and is kept.  The continuation carries the
-- phase, which a hash query never moves.
hashJ : Tbl → (Tbl → JSt) → Pt → Dₚ (JSt × (Neg Lkᴵᶜ ⊎ Pos (Lkᴵ ⊗ᴵ Advᴵᶜ)))
hashJ t φ x = case lookupPt t x of λ where
  (just d) → returnₚ (φ t , inj₂ (inj₁ (digˢ d)))
  nothing  → uniformₚ k >>=ₚ λ h → returnₚ (φ ((x , h) ∷ t) , inj₂ (inj₁ (digˢ h)))

hashJ-hit : (t : Tbl) (φ : Tbl → JSt) (x : Pt) (d : Dig) → lookupPt t x ≡ just d
          → hashJ t φ x ≈ₚ returnₚ (φ t , inj₂ (inj₁ (digˢ d)))
hashJ-hit t φ x d eq rewrite eq = ≈ₚ-refl _

hashJ-miss : (t : Tbl) (φ : Tbl → JSt) (x : Pt) → lookupPt t x ≡ nothing
           → hashJ t φ x
             ≈ₚ (uniformₚ k >>=ₚ λ h → returnₚ (φ ((x , h) ∷ t) , inj₂ (inj₁ (digˢ h))))
hashJ-miss t φ x eq rewrite eq = ≈ₚ-refl _

jStep : JSt × (Pos Lkᴵᶜ ⊎ Neg (Lkᴵ ⊗ᴵ Advᴵᶜ))
      → Dₚ (JSt × (Neg Lkᴵᶜ ⊎ Pos (Lkᴵ ⊗ᴵ Advᴵᶜ)))
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
stateʲ = record { obj = JSt ; point = λ _ → returnₚ (preʲ []) ; discard = λ _ → returnₚ tt }

simJ : Proc Lkᴵᶜ (Lkᴵ ⊗ᴵ Advᴵᶜ)
simJ = mk stateʲ jStep
