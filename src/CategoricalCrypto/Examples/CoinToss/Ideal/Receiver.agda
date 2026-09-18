{-# OPTIONS --safe --without-K --guardedness #-}

-- The ideal coin and the joint simulator for Blum coin-tossing over `F_com`
-- against a corrupted RECEIVER.
--
-- `Examples.CoinToss.Ideal` is the corrupted-committer pair; the two
-- corruptions are different ports (`docs/fcom-hiding.md`), so this is a second
-- functionality and a second simulator, not an instance of that one.
--
-- `Fcoinʰ` leaks before it delivers, as `Fcoin` does and for the same reason:
-- the corrupted receiver learns the honest committer's share at the opening
-- and only then does the honest party collect, so the coin is unfair in
-- Cleve's sense.  What it leaks is in two steps — `startᵏʰ` when the honest
-- committer is started, `coinᵏʰ c` when the simulator buys the bit — and the
-- bit is the functionality's OWN uniform draw, read by nothing the adversary
-- says.
--
-- There is no abort query, because the composite has no abort: `F_com`'s
-- refusal `nakᴱ` reaches the stage only through the resource's `rejᴿ`, which
-- `Examples.ROCommitment.Hiding.downᶠʰ` never asks for.  A corrupted receiver
-- that wants the toss not to finish simply never sends its share, and in both
-- worlds the honest party then produces nothing.
--
-- `simJʰ` is joint in `docs/coin-toss.md` §5 Form B's sense: one machine on
-- both halves of the hybrid's grade.  It runs the random oracle itself — the
-- table is its state, nothing sits below it but the coin — publishes the
-- receipt, and at the corrupted receiver's share `b₂` buys the coin and
-- reports the committed bit as `bitᶠ (c xor b₂)`, which is what makes the
-- hybrid's `b₁ xor b₂` land on `Fcoinʰ`'s own `c`.

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

module CategoricalCrypto.Examples.CoinToss.Ideal.Receiver (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss.Hiding k
open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
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

-- Not started, started and undrawn, drawn and held, released.
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
stateᵏʰ = record { obj = FStʰ ; point = λ _ → returnₚ freshᵏʰ ; discard = λ _ → returnₚ tt }

Fcoinʰ : Proc unitᴵ (Lkᴵᶜʰ ⊗ᴵ Honᴵᶜʰ)
Fcoinʰ = mk stateᵏʰ coinStepʰ

------------------------------------------------------------------------
-- The joint simulator

-- The oracle table it answers from, plus how far the toss has got: before the
-- start, the receipt published, the share heard and the coin outstanding,
-- done.
data JStʰ : Set where
  preʲʰ : Tbl → JStʰ
  midʲʰ : Tbl → JStʰ
  askʲʰ : Tbl → Bool → JStʰ
  endʲʰ : Tbl → JStʰ

-- `Examples.ROCommitment.Resource`'s oracle clause with the table in the
-- simulator's own state; the continuation carries the phase, which a hash
-- query never moves.  This is `Examples.CoinToss.Ideal.hashJ` at the other
-- corruption's ports.
hashJʰ : Tbl → (Tbl → JStʰ) → Pt → Dₚ (JStʰ × (Neg Lkᴵᶜʰ ⊎ Pos (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ)))
hashJʰ t φ x = case lookupPt t x of λ where
  (just d) → returnₚ (φ t , inj₂ (inj₁ (digᶠ d)))
  nothing  → uniformₚ k >>=ₚ λ h → returnₚ (φ ((x , h) ∷ t) , inj₂ (inj₁ (digᶠ h)))

hashJʰ-hit : (t : Tbl) (φ : Tbl → JStʰ) (x : Pt) (d : Dig) → lookupPt t x ≡ just d
           → hashJʰ t φ x ≈ₚ returnₚ (φ t , inj₂ (inj₁ (digᶠ d)))
hashJʰ-hit t φ x d eq rewrite eq = ≈ₚ-refl _

hashJʰ-miss : (t : Tbl) (φ : Tbl → JStʰ) (x : Pt) → lookupPt t x ≡ nothing
            → hashJʰ t φ x
              ≈ₚ (uniformₚ k >>=ₚ λ h → returnₚ (φ ((x , h) ∷ t) , inj₂ (inj₁ (digᶠ h))))
hashJʰ-miss t φ x eq rewrite eq = ≈ₚ-refl _

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
stateʲʰ = record { obj = JStʰ ; point = λ _ → returnₚ (preʲʰ []) ; discard = λ _ → returnₚ tt }

simJʰ : Proc Lkᴵᶜʰ (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ)
simJʰ = mk stateʲʰ jStepʰ
