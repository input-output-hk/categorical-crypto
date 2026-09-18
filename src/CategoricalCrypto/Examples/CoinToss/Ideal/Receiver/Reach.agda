{-# OPTIONS --safe --without-K --guardedness #-}

-- The reachable configurations of Blum coin-tossing over `F_com` over the
-- concrete resource, corrupted RECEIVER — as TWO machines, differing only in
-- when the honest committer's share is drawn.
--
-- `Examples.CoinToss.Ideal.Reach` needs one such machine, because there the
-- draw and its use land in the same activation.  Here they do not: the share
-- `b₁` is drawn when the environment starts the committer (`goᶜ`) and is first
-- read when the corrupted receiver answers with its own share (`shareᴬʰ b₂`).
-- The ideal coin cannot draw at `goᶜ` — its bit would have to be `b₁ xor b₂`
-- at a `b₂` not yet chosen — so on the ideal side the draw sits at the second
-- activation, and no state map relates the two (`docs/coin-toss.md` §5).
--
--   • `eagerᶜʰ` draws at `goᶜ`; `Receiver.Hybrid` simulates it into the hybrid.
--   • `deferᶜʰ` draws at `shareᴬʰ`; `Receiver.Machine` simulates it into the
--     ideal side, and moves the draw between the two at the RUN layer with
--     `GamePlaying.Defer.Run`.
--
-- Everything else is shared: the oracle table, the three phases, and the
-- output letters.

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

module CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Reach (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss.Hiding k
open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Hiding k

open Core (𝒱ₚ 0ℓ)

-- The grade the hybrid carries, in the two brackets the associator that
-- `UC.Asymptotic.Compose._∙ᶠ_` leaves in front of it sits between.
Cⁱʰ Cᵗʰ : Iface
Cⁱʰ = Lkᴵʰ ⊗ᴵ (Advᴵᶜʰ ⊗ᴵ Honᴵᶜʰ)
Cᵗʰ = (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ) ⊗ᴵ Honᴵᶜʰ

------------------------------------------------------------------------
-- The oracle, at either state space

-- The lazy table, generic in the phase the caller carries: both machines
-- answer an oracle query the same way and neither moves phase at one.
hashᶜʰ : {S : Set} → Tbl → (Tbl → S) → Pt → Dₚ (S × (Neg unitᴵ ⊎ Pos Cⁱʰ))
hashᶜʰ t φ x = case lookupPt t x of λ where
  (just d) → returnₚ (φ t , inj₂ (inj₁ (digᶠ d)))
  nothing  → uniformₚ k >>=ₚ λ h → returnₚ (φ ((x , h) ∷ t) , inj₂ (inj₁ (digᶠ h)))

hashᶜʰ-hit : {S : Set} (t : Tbl) (φ : Tbl → S) (x : Pt) (d : Dig) → lookupPt t x ≡ just d
           → hashᶜʰ t φ x ≈ₚ returnₚ (φ t , inj₂ (inj₁ (digᶠ d)))
hashᶜʰ-hit t φ x d eq rewrite eq = ≈refl

hashᶜʰ-miss : {S : Set} (t : Tbl) (φ : Tbl → S) (x : Pt) → lookupPt t x ≡ nothing
            → hashᶜʰ t φ x
              ≈ₚ (uniformₚ k >>=ₚ λ h → returnₚ (φ ((x , h) ∷ t) , inj₂ (inj₁ (digᶠ h))))
hashᶜʰ-miss t φ x eq rewrite eq = ≈refl

------------------------------------------------------------------------
-- Drawing at `goᶜ`

-- Before the start, committed to `b₁`, opened against the receiver's `b₂`,
-- collected.  `b₁` is kept to the end because the commitment cell holds it.
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
stateᴱ = record { obj = EStʰ ; point = λ _ → returnₚ (preᴱ []) ; discard = λ _ → returnₚ tt }

eagerᶜʰ′ : Proc unitᴵ Cⁱʰ
eagerᶜʰ′ = mk stateᴱ eStep

------------------------------------------------------------------------
-- …and drawing at `shareᴬʰ`

-- The same phases with the share unborn until it is published.  `endᴰ` keeps
-- it, which is what makes the relation to `eagerᶜʰ` a pointwise equality
-- rather than an existential.
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
stateᴰ = record { obj = DStʰ ; point = λ _ → returnₚ (preᴰ []) ; discard = λ _ → returnₚ tt }

deferᶜʰ′ : Proc unitᴵ Cⁱʰ
deferᶜʰ′ = mk stateᴰ dStep

------------------------------------------------------------------------
-- …at the bracket the grade is compared in

-- `(λ a → a)` and not `id`: this has to be the SAME term
-- `UC.Machine.Wire.wire-∘ᴹ` produces, and neither side reduces at a variable.
eagerᶜʰ : Proc unitᴵ Cᵗʰ
eagerᶜʰ = sandwichᴹ eagerᶜʰ′ (Sum.map (λ a → a) ⊎assocʳ) (Sum.map (λ a → a) ⊎assocˡ)

deferᶜʰ : Proc unitᴵ Cᵗʰ
deferᶜʰ = sandwichᴹ deferᶜʰ′ (Sum.map (λ a → a) ⊎assocʳ) (Sum.map (λ a → a) ⊎assocˡ)
