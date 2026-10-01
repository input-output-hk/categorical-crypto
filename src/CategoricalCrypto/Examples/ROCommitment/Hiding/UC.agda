{-# OPTIONS --safe --without-K --guardedness #-}

-- The corrupted-receiver machines at the UC model, and the programming
-- simulator's query certificate.  The emulation is approximate (the ε against
-- the protocol's game transcription is `Examples.ROCommitment.Hiding.Defer.
-- hiding-bound-total`), so there is no `≈ᵁ` here.

open import Categories.LocallyGraded.SubCategory

open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Function.Base

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Model.Dominated
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.Examples.ROCommitment.Hiding.UC (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Hiding k

open GradedSubCat gradingᵒ using (Pred)

------------------------------------------------------------------------
-- The images

realʰᵒ : ifaceᵒ Resᴵ ⇒ T₀ (ifaceᵒ Advᴵʰ) (ifaceᵒ Honᴵʰ)
realʰᵒ = gradedᵒ realʰ

idealʰᵒ : ifaceᵒ Resᴵ ⇒ T₀ (ifaceᵒ Lkᴵʰ) (ifaceᵒ Honᴵʰ)
idealʰᵒ = gradedᵒ idealʰ

simʰᵒ : ifaceᵒ Lkᴵʰ ⇒ ifaceᵒ Advᴵʰ
simʰᵒ = procᵒ simulatorʰ

------------------------------------------------------------------------
-- The honest committer spends one oracle call per activation from above

comCert : Certified 1 realʰ
comCert = qbᵢ-upward _ _ _ onL cohL
  where
  -- Letter before state, as in `Examples.ROCommitment.UC.recvCert`.
  onL : (s : HStʰ) (a : Pos Resᴵ) → Dₚ (Ans (λ _ → 0) (Neg Resᴵ) (Pos (Advᴵʰ ⊗ᴵ Honᴵʰ)) 0)
  onL _          rcptᴿ    = botₚ
  onL _          (outᴿ _) = botₚ
  onL _          rejᴿ     = botₚ
  onL (ownʰ b r) (digᴿ d) = returnₚ (inj₂ ((readyʰ (boundᴴ b r) , z≤n) , inj₁ (comᴿᶜ d)))
  onL (relayʰ h) (digᴿ d) = returnₚ (inj₂ ((readyʰ h , z≤n) , inj₁ (ansᴿᶜ d)))
  onL (readyʰ _) (digᴿ _) = botₚ

  cohL : (s : HStʰ) (a : Pos Resᴵ) → mapₚ forget (onL s a) ≈ₚ realStepʰ (s , inj₁ a)
  cohL _          rcptᴿ    = bot-bind-≈ₚ _
  cohL _          (outᴿ _) = bot-bind-≈ₚ _
  cohL _          rejᴿ     = bot-bind-≈ₚ _
  cohL (ownʰ _ _) (digᴿ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (relayʰ _) (digᴿ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (readyʰ _) (digᴿ _) = bot-bind-≈ₚ _

comQB : Pred 1⁺ (gradedᵒ realʰ)
comQB = qb-gradedᵒ (certified⇒QB comCert)

------------------------------------------------------------------------
-- The allowance

-- No `UC.QueryBound.Exact` ledger exists for this simulator: whether a query
-- costs a relay depends on whether it names the programmed point, a fact about
-- the state, while `Exact` weighs an activation by its letter alone.
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
  onL _ _                         = botₚ

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

idealʰQB : QB 1 idealʰ
idealʰQB = qb-wire upᶠʰ downᶠʰ
