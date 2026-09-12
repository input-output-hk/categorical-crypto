{-# OPTIONS --safe --without-K --guardedness #-}

-- The hiding-side coin-toss stage at the UC model, and the two certificates
-- the composition theorem demands.
--
-- Both are at rate 1 and both have a potential that is constantly zero: an
-- activation from above buys exactly one downward message and nothing is ever
-- owed afterwards.  For the honest committer (`Examples.ROCommitment.Hiding`)
-- that message is the oracle call it makes for its own commitment or for the
-- corrupted receiver's query; for the coin-toss stage it is the `commitᴱ` or
-- the `openᴱ` that drives `F_com`.

open import Data.Bool.Base using (_xor_)
open import Data.Nat.Base using (ℕ; s≤s; z≤n)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Function.Base using (_∘′_)

open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin using (coinₚ)
open import ProbabilisticLogic.Dp.Reasoning
open import ProbabilisticLogic.Dp.Uniform using (uniformₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Model.Dominated using (qb-gradedᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Seal using (gradedᵒ; ifaceᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound using (Certified; certified⇒QB; forget)

module CategoricalCrypto.Examples.CoinToss.Hiding.UC (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss.Hiding k
open import CategoricalCrypto.Examples.ROCommitment k using (Resᴵ; hashᴿ; digᴿ; rcptᴿ; outᴿ; rejᴿ)
open import CategoricalCrypto.Examples.ROCommitment.Hiding k

open Budget budgetᵒ using (QB)

------------------------------------------------------------------------
-- The image

tossʰᵒ : ifaceᵒ Honᴵʰ ⇒ T₀ (ifaceᵒ Advᴵᶜʰ) (ifaceᵒ Honᴵᶜʰ)
tossʰᵒ = gradedᵒ tossʰ

------------------------------------------------------------------------
-- One drive of `F_com` per activation from above

tossʰCert : Certified 1 tossʰ
tossʰCert = record
  { Φ      = λ _ → 0
  ; pointᵍ = returnₚ (freshᵗ , z≤n)
  ; coh₀   = >>=ₚ-identityˡ (freshᵗ , z≤n) (returnₚ ∘′ proj₁)
  ; onLᵍ   = onL
  ; onRᵍ   = onR
  ; cohL   = cohL
  ; cohR   = cohR
  }
  where
  onL : (s : QSt) (a : Pos Honᴵʰ) → Dₚ _
  onL (comᵗ _)    nakᴱ = returnₚ (inj₂ ((doneᵗ , z≤n) , inj₂ abortedᶜʰ))
  onL (openᵗ _ _) nakᴱ = returnₚ (inj₂ ((doneᵗ , z≤n) , inj₂ abortedᶜʰ))
  onL freshᵗ      nakᴱ = botₚ
  onL doneᵗ       nakᴱ = botₚ

  onR : (s : QSt) (b : Neg (Advᴵᶜʰ ⊗ᴵ Honᴵᶜʰ)) → Dₚ _
  onR (comᵗ b₁)    (inj₁ (shareᴬʰ b₂)) =
    returnₚ (inj₁ ((openᵗ b₁ b₂ , s≤s z≤n) , openᴱ))
  onR freshᵗ       (inj₂ goᶜ)          =
    coinₚ uniform-Bool >>=ₚ λ b₁ → returnₚ (inj₁ ((comᵗ b₁ , s≤s z≤n) , commitᴱ b₁))
  onR (openᵗ b₁ b₂) (inj₂ getᶜ)        =
    returnₚ (inj₂ ((doneᵗ , z≤n) , inj₂ (tossedᶜʰ (b₁ xor b₂))))
  onR freshᵗ        (inj₁ _)           = botₚ
  onR (openᵗ _ _)   (inj₁ _)           = botₚ
  onR doneᵗ         (inj₁ _)           = botₚ
  onR (comᵗ _)      (inj₂ goᶜ)         = botₚ
  onR (openᵗ _ _)   (inj₂ goᶜ)         = botₚ
  onR doneᵗ         (inj₂ goᶜ)         = botₚ
  onR freshᵗ        (inj₂ getᶜ)        = botₚ
  onR (comᵗ _)      (inj₂ getᶜ)        = botₚ
  onR doneᵗ         (inj₂ getᶜ)        = botₚ

  cohL : (s : QSt) (a : Pos Honᴵʰ) → mapₚ forget (onL s a) ≈ₚ τStep (s , inj₁ a)
  cohL (comᵗ _)    nakᴱ = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (openᵗ _ _) nakᴱ = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL freshᵗ      nakᴱ = bot-bind-≈ₚ _
  cohL doneᵗ       nakᴱ = bot-bind-≈ₚ _

  cohR : (s : QSt) (b : Neg (Advᴵᶜʰ ⊗ᴵ Honᴵᶜʰ))
       → mapₚ forget (onR s b) ≈ₚ τStep (s , inj₂ b)
  cohR (comᵗ _)     (inj₁ (shareᴬʰ _)) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR freshᵗ       (inj₂ goᶜ)         = map-bind (coinₚ uniform-Bool) _ forget
                                       ⟨≈⟩ bindᶠ λ _ → >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (openᵗ _ _)  (inj₂ getᶜ)        = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR freshᵗ       (inj₁ (shareᴬʰ _)) = bot-bind-≈ₚ _
  cohR (openᵗ _ _)  (inj₁ (shareᴬʰ _)) = bot-bind-≈ₚ _
  cohR doneᵗ        (inj₁ (shareᴬʰ _)) = bot-bind-≈ₚ _
  cohR (comᵗ _)     (inj₂ goᶜ)         = bot-bind-≈ₚ _
  cohR (openᵗ _ _)  (inj₂ goᶜ)         = bot-bind-≈ₚ _
  cohR doneᵗ        (inj₂ goᶜ)         = bot-bind-≈ₚ _
  cohR freshᵗ       (inj₂ getᶜ)        = bot-bind-≈ₚ _
  cohR (comᵗ _)     (inj₂ getᶜ)        = bot-bind-≈ₚ _
  cohR doneᵗ        (inj₂ getᶜ)        = bot-bind-≈ₚ _

tossʰQB : QB 1 tossʰᵒ
tossʰQB = qb-gradedᵒ (certified⇒QB tossʰCert)

------------------------------------------------------------------------
-- The honest committer spends one oracle call per activation from above

comCert : Certified 1 realʰ
comCert = record
  { Φ      = λ _ → 0
  ; pointᵍ = returnₚ (readyʰ freshᴴ , z≤n)
  ; coh₀   = >>=ₚ-identityˡ (readyʰ freshᴴ , z≤n) (returnₚ ∘′ proj₁)
  ; onLᵍ   = onL
  ; onRᵍ   = onR
  ; cohL   = cohL
  ; cohR   = cohR
  }
  where
  -- The letter is split before the state, so that a `cohL` clause at a
  -- VARIABLE state still reduces.
  onL : (s : HStʰ) (a : Pos Resᴵ) → Dₚ _
  onL _          rcptᴿ    = botₚ
  onL _          (outᴿ _) = botₚ
  onL _          rejᴿ     = botₚ
  onL (ownʰ b r) (digᴿ d) = returnₚ (inj₂ ((readyʰ (boundᴴ b r) , z≤n) , inj₁ (comᴿᶜ d)))
  onL (relayʰ h) (digᴿ d) = returnₚ (inj₂ ((readyʰ h , z≤n) , inj₁ (ansᴿᶜ d)))
  onL (readyʰ _) (digᴿ _) = botₚ

  onR : (s : HStʰ) (b : Neg (Advᴵʰ ⊗ᴵ Honᴵʰ)) → Dₚ _
  onR (readyʰ h)            (inj₁ (askᴿᶜ x))  =
    returnₚ (inj₁ ((relayʰ h , s≤s z≤n) , hashᴿ x))
  onR (readyʰ freshᴴ)       (inj₂ (commitᴱ b)) =
    uniformₚ k >>=ₚ λ r → returnₚ (inj₁ ((ownʰ b r , s≤s z≤n) , hashᴿ (b ∷ᵛ r)))
  onR (readyʰ (boundᴴ b r)) (inj₂ (commitᴱ _)) =
    returnₚ (inj₂ ((readyʰ (boundᴴ b r) , z≤n) , inj₂ nakᴱ))
  onR (readyʰ shownᴴ)       (inj₂ (commitᴱ _)) =
    returnₚ (inj₂ ((readyʰ shownᴴ , z≤n) , inj₂ nakᴱ))
  onR (readyʰ (boundᴴ b r)) (inj₂ openᴱ)       =
    returnₚ (inj₂ ((readyʰ shownᴴ , z≤n) , inj₁ (opnᴿᶜ b r)))
  onR (readyʰ freshᴴ)       (inj₂ openᴱ)       =
    returnₚ (inj₂ ((readyʰ freshᴴ , z≤n) , inj₂ nakᴱ))
  onR (readyʰ shownᴴ)       (inj₂ openᴱ)       =
    returnₚ (inj₂ ((readyʰ shownᴴ , z≤n) , inj₂ nakᴱ))
  onR (ownʰ _ _)            (inj₁ _)           = botₚ
  onR (relayʰ _)            (inj₁ _)           = botₚ
  onR (ownʰ _ _)            (inj₂ _)           = botₚ
  onR (relayʰ _)            (inj₂ _)           = botₚ

  cohL : (s : HStʰ) (a : Pos Resᴵ) → mapₚ forget (onL s a) ≈ₚ realStepʰ (s , inj₁ a)
  cohL _          rcptᴿ    = bot-bind-≈ₚ _
  cohL _          (outᴿ _) = bot-bind-≈ₚ _
  cohL _          rejᴿ     = bot-bind-≈ₚ _
  cohL (ownʰ _ _) (digᴿ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (relayʰ _) (digᴿ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (readyʰ _) (digᴿ _) = bot-bind-≈ₚ _

  cohR : (s : HStʰ) (b : Neg (Advᴵʰ ⊗ᴵ Honᴵʰ))
       → mapₚ forget (onR s b) ≈ₚ realStepʰ (s , inj₂ b)
  cohR (readyʰ _)          (inj₁ (askᴿᶜ _))   = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (readyʰ freshᴴ)     (inj₂ (commitᴱ _)) = map-bind (uniformₚ k) _ forget
                                              ⟨≈⟩ bindᶠ λ _ → >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (readyʰ (boundᴴ _ _)) (inj₂ (commitᴱ _)) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (readyʰ shownᴴ)     (inj₂ (commitᴱ _)) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (readyʰ (boundᴴ _ _)) (inj₂ openᴱ)     = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (readyʰ freshᴴ)     (inj₂ openᴱ)       = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (readyʰ shownᴴ)     (inj₂ openᴱ)       = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (ownʰ _ _)          (inj₁ (askᴿᶜ _))   = bot-bind-≈ₚ _
  cohR (relayʰ _)          (inj₁ (askᴿᶜ _))   = bot-bind-≈ₚ _
  cohR (ownʰ _ _)          (inj₂ (commitᴱ _)) = bot-bind-≈ₚ _
  cohR (relayʰ _)          (inj₂ (commitᴱ _)) = bot-bind-≈ₚ _
  cohR (ownʰ _ _)          (inj₂ openᴱ)       = bot-bind-≈ₚ _
  cohR (relayʰ _)          (inj₂ openᴱ)       = bot-bind-≈ₚ _

comQB : QB 1 (gradedᵒ realʰ)
comQB = qb-gradedᵒ (certified⇒QB comCert)
