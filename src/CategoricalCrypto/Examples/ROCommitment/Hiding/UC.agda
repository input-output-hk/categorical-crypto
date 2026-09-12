{-# OPTIONS --safe --without-K --guardedness #-}

-- The three machines at the UC model, and what the programming simulator
-- spends.
--
-- The grade is `ifaceᵒ Advᴵʰ`, inhabited by the corrupted receiver's oracle
-- query, so `procᵒ simulatorʰ` is not a scalar and nothing here is in reach of
-- `UC.Seam.Grounded.subBlind`.  There is no `≈ᵁ` between `realʰᵒ` and
-- `sub simʰᵒ ∘ idealʰᵒ`: the emulation is approximate and its ε is
-- `Examples.ROCommitment.Hiding.Game`.
--
-- The allowance is ONE downward message per activation from above and none at
-- all from below, with a potential that is constantly zero: the simulator
-- answers the programmed point out of its own record and relays every other,
-- and it never owes a second message.  That ceiling is EXACT as a ceiling and
-- cannot be sharpened to a `UC.QueryBound.Exact` ledger — see the note on
-- `simCertʰ`.

open import Data.Bool.Base using (Bool)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; s≤s; z≤n)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Function.Base using (_∘′_; case_of_)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning
open import ProbabilisticLogic.Dp.Uniform

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Model.Seal using (gradedᵒ; ifaceᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound using
  (Ans; Certified; QB; certified⇒QB; forget)

module CategoricalCrypto.Examples.ROCommitment.Hiding.UC (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k using (Resᴵ)
open import CategoricalCrypto.Examples.ROCommitment.Extraction k using (Dig)
open import CategoricalCrypto.Examples.ROCommitment.Hiding k

------------------------------------------------------------------------
-- The images

realʰᵒ : ifaceᵒ Resᴵ ⇒ T₀ (ifaceᵒ Advᴵʰ) (ifaceᵒ Honᴵʰ)
realʰᵒ = gradedᵒ realʰ

idealʰᵒ : ifaceᵒ Resᴵ ⇒ T₀ (ifaceᵒ Lkᴵʰ) (ifaceᵒ Honᴵʰ)
idealʰᵒ = gradedᵒ idealʰ

simʰᵒ : ifaceᵒ Lkᴵʰ ⇒ ifaceᵒ Advᴵʰ
simʰᵒ = procᵒ simulatorʰ

------------------------------------------------------------------------
-- The allowance

-- Nothing is ever owed: every message from below is answered upward, and the
-- one message an activation from above can cost is spent in the same step.
--
-- This is where an EXACT ledger stops being available, and the reason is the
-- programming itself.  `UC.QueryBound.Exact` weighs an activation by a
-- function of the LETTER alone, and whether a query costs a relay depends on
-- whether the letter names the programmed point — a fact about the state, not
-- about the letter.  So the exact count is `#queries − #(queries at the
-- programmed point)`, which no `Exact` weighting expresses, and the amortised
-- ceiling below is the sharpest statement of this shape.
Φᵖ : SStʰ → ℕ
Φᵖ _ = 0

simCertʰ : Certified 1 simulatorʰ
simCertʰ = record
  { Φ      = Φᵖ
  ; pointᵍ = returnₚ (idleᵖ blankᵖ , z≤n)
  ; coh₀   = >>=ₚ-identityˡ (idleᵖ blankᵖ , z≤n) (returnₚ ∘′ proj₁)
  ; onLᵍ   = onL
  ; onRᵍ   = onR
  ; cohL   = cohL
  ; cohR   = cohR
  }
  where
  -- The two refined answers a draw lands on, named: `_>>=ₚ_` is a coinductive
  -- record, so `map-bind` cannot recover the continuation by unification.
  pubᴬ : Dig → Ans Φᵖ (Neg Lkᴵʰ) (Pos Advᴵʰ) 0
  pubᴬ c = inj₂ ((idleᵖ (pubᵖ c) , z≤n) , comᴿᶜ c)

  pinᴬ : Dig → Bool → Dig → Ans Φᵖ (Neg Lkᴵʰ) (Pos Advᴵʰ) 0
  pinᴬ c b r = inj₂ ((idleᵖ (pinᵖ (b ∷ᵛ r) c) , z≤n) , opnᴿᶜ b r)

  onL : (s : SStʰ) (a : Pos Lkᴵʰ) → Dₚ _
  onL (relayᵖ p)       (digᶠ d)  = returnₚ (inj₂ ((idleᵖ p , z≤n) , ansᴿᶜ d))
  onL (idleᵖ blankᵖ)   rcptᶠ     = uniformₚ k >>=ₚ λ c → returnₚ (pubᴬ c)
  onL (idleᵖ (pubᵖ c)) (bitᶠ b)  = uniformₚ k >>=ₚ λ r → returnₚ (pinᴬ c b r)
  onL (idleᵖ blankᵖ)     (digᶠ _) = botₚ
  onL (idleᵖ (pubᵖ _))   (digᶠ _) = botₚ
  onL (idleᵖ (pinᵖ _ _)) (digᶠ _) = botₚ
  onL (idleᵖ (pubᵖ _))   rcptᶠ    = botₚ
  onL (idleᵖ (pinᵖ _ _)) rcptᶠ    = botₚ
  onL (idleᵖ blankᵖ)     (bitᶠ _) = botₚ
  onL (idleᵖ (pinᵖ _ _)) (bitᶠ _) = botₚ
  onL (relayᵖ _)         rcptᶠ    = botₚ
  onL (relayᵖ _)         (bitᶠ _) = botₚ

  onR : (s : SStʰ) (b : Neg Advᴵʰ) → Dₚ _
  onR (idleᵖ p)  (askᴿᶜ x) = case pinnedʰ p x of λ where
    (just c) → returnₚ (inj₂ ((idleᵖ p  , z≤n)     , ansᴿᶜ c))
    nothing  → returnₚ (inj₁ ((relayᵖ p , s≤s z≤n) , relayᶠ x))
  onR (relayᵖ _) (askᴿᶜ _) = botₚ

  cohL : (s : SStʰ) (a : Pos Lkᴵʰ) → mapₚ forget (onL s a) ≈ₚ simStepʰ (s , inj₁ a)
  cohL (relayᵖ _)         (digᶠ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (idleᵖ blankᵖ)     rcptᶠ    =
    map-bind (uniformₚ k) (λ c → returnₚ (pubᴬ c)) forget
    ⟨≈⟩ bindᶠ (λ c → >>=ₚ-identityˡ (pubᴬ c) (returnₚ ∘′ forget))
  cohL (idleᵖ (pubᵖ c))   (bitᶠ b) =
    map-bind (uniformₚ k) (λ r → returnₚ (pinᴬ c b r)) forget
    ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ (pinᴬ c b r) (returnₚ ∘′ forget))
  cohL (idleᵖ blankᵖ)     (digᶠ _)  = bot-bind-≈ₚ _
  cohL (idleᵖ (pubᵖ _))   (digᶠ _)  = bot-bind-≈ₚ _
  cohL (idleᵖ (pinᵖ _ _)) (digᶠ _)  = bot-bind-≈ₚ _
  cohL (idleᵖ (pubᵖ _))   rcptᶠ     = bot-bind-≈ₚ _
  cohL (idleᵖ (pinᵖ _ _)) rcptᶠ     = bot-bind-≈ₚ _
  cohL (idleᵖ blankᵖ)     (bitᶠ _)  = bot-bind-≈ₚ _
  cohL (idleᵖ (pinᵖ _ _)) (bitᶠ _)  = bot-bind-≈ₚ _
  cohL (relayᵖ _)         rcptᶠ     = bot-bind-≈ₚ _
  cohL (relayᵖ _)         (bitᶠ _)  = bot-bind-≈ₚ _

  cohR : (s : SStʰ) (b : Neg Advᴵʰ) → mapₚ forget (onR s b) ≈ₚ simStepʰ (s , inj₂ b)
  cohR (idleᵖ p)  (askᴿᶜ x) with pinnedʰ p x
  ... | just _  = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  ... | nothing = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (relayᵖ _) (askᴿᶜ _) = bot-bind-≈ₚ _

simQBʰ : QB 1 simulatorʰ
simQBʰ = certified⇒QB simCertʰ
