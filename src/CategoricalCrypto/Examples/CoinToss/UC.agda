{-# OPTIONS --safe --without-K --guardedness #-}

-- The coin-toss stage at the UC model, and the two query certificates the
-- composition theorem demands of the morphisms it moves.
--
-- `UC.Asymptotic.Compose.UC-composeᵉ` asks for a bound on the INNER real
-- process and on the OUTER ideal one, and both are theorems here rather than
-- premises: the commitment's honest receiver relays at most one oracle query
-- per adversary message (`recvCert`), and the coin-toss stage makes NO downward
-- call at all (`tossCert`) — its domain `Honᴵ` has an empty `Neg`, so a
-- certificate at rate `0` is available and `UC.QueryBound.qbᵢ-closed`'s reason
-- is the same one.

open import Class.DecEq

open import Data.Bool.Base using (_xor_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; s≤s; z≤n)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Function.Base using (_∘′_)
open import Relation.Nullary.Decidable.Core using (⌊_⌋)

open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin using (coinₚ)
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Model.Dominated using (qb-gradedᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Seal using (gradedᵒ; ifaceᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.QueryBound using (Certified; certified⇒QB; forget)

module CategoricalCrypto.Examples.CoinToss.UC (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss k
open import CategoricalCrypto.Examples.ROCommitment k

open Budget budgetᵒ using (QB)

------------------------------------------------------------------------
-- The images

-- The commitment's two worlds are `Examples.ROCommitment.UC`'s; only the stage
-- above them is new, and its domain IS their codomain.
tossᵒ : ifaceᵒ Honᴵ ⇒ T₀ (ifaceᵒ Advᴵᶜ) (ifaceᵒ Honᴵᶜ)
tossᵒ = gradedᵒ toss

------------------------------------------------------------------------
-- The coin-toss stage spends nothing

-- `Neg Honᴵ` is empty, so no output of `toss` is downward: the potential stays
-- at zero and the rate is zero, whatever the stage does above it.
tossCert : Certified 0 toss
tossCert = record
  { Φ      = λ _ → 0
  ; pointᵍ = returnₚ (freshᵖ , z≤n)
  ; coh₀   = >>=ₚ-identityˡ (freshᵖ , z≤n) (returnₚ ∘′ proj₁)
  ; onLᵍ   = onL
  ; onRᵍ   = λ where _ (inj₁ ()) ; _ (inj₂ ())
  ; cohL   = cohL
  ; cohR   = λ where _ (inj₁ ()) ; _ (inj₂ ())
  }
  where
  onL : (s : PSt) (a : Pos Honᴵ) → Dₚ _
  onL freshᵖ     rcptᴴ        = coinₚ uniform-Bool >>=ₚ λ b₂ →
                                 returnₚ (inj₂ ((heldᵖ b₂ , z≤n) , inj₁ (shareᴬ b₂)))
  onL (heldᵖ b₂) (openedᴴ b₁) = returnₚ (inj₂ ((doneᵖ , z≤n) , inj₂ (tossedᶜ (b₁ xor b₂))))
  onL (heldᵖ _)  refusedᴴ     = returnₚ (inj₂ ((doneᵖ , z≤n) , inj₂ abortedᶜ))
  onL freshᵖ     (openedᴴ _)  = botₚ
  onL freshᵖ     refusedᴴ     = botₚ
  onL (heldᵖ _)  rcptᴴ        = botₚ
  onL doneᵖ      _            = botₚ

  cohL : (s : PSt) (a : Pos Honᴵ) → mapₚ forget (onL s a) ≈ₚ πStep (s , inj₁ a)
  cohL freshᵖ     rcptᴴ        = map-bind (coinₚ uniform-Bool) _ forget
                               ⟨≈⟩ bindᶠ λ _ → >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (heldᵖ _)  (openedᴴ _)  = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (heldᵖ _)  refusedᴴ     = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL freshᵖ     (openedᴴ _)  = bot-bind-≈ₚ _
  cohL freshᵖ     refusedᴴ     = bot-bind-≈ₚ _
  cohL (heldᵖ _)  rcptᴴ        = bot-bind-≈ₚ _
  cohL doneᵖ      rcptᴴ        = bot-bind-≈ₚ _
  cohL doneᵖ      (openedᴴ _)  = bot-bind-≈ₚ _
  cohL doneᵖ      refusedᴴ     = bot-bind-≈ₚ _

tossQB : QB 0 tossᵒ
tossQB = qb-gradedᵒ (certified⇒QB tossCert)

------------------------------------------------------------------------
-- The honest receiver relays at most one query per message

-- An activation from above buys one downward oracle call and the answer to it
-- only returns, so the potential is constantly zero.  This is
-- `UC.QueryBound.qb-oneCall`'s content at a machine that is not a `morphism`
-- image, and that lemma is stated only at one, so it is written out.
recvCert : Certified 1 real
recvCert = record
  { Φ      = λ _ → 0
  ; pointᵍ = returnₚ (waitᴿ nothing , z≤n)
  ; coh₀   = >>=ₚ-identityˡ (waitᴿ nothing , z≤n) (returnₚ ∘′ proj₁)
  ; onLᵍ   = onL
  ; onRᵍ   = onR
  ; cohL   = cohL
  ; cohR   = cohR
  }
  where
  -- The letter is split before the state, so that a `cohL` clause at a
  -- VARIABLE state still reduces.
  onL : (s : RSt) (a : Pos Resᴵ) → Dₚ _
  onL _            rcptᴿ    = botₚ
  onL _            (outᴿ _) = botₚ
  onL _            rejᴿ     = botₚ
  onL (relayᴿ m)   (digᴿ d) = returnₚ (inj₂ ((waitᴿ m , z≤n) , inj₁ (ansᴬ d)))
  onL (checkᴿ c b) (digᴿ d) =
    returnₚ (inj₂ ((waitᴿ (just c) , z≤n) , inj₂ (verdict b ⌊ d ≟ c ⌋)))
  onL (waitᴿ _)    (digᴿ _) = botₚ

  onR : (s : RSt) (b : Neg (Advᴵ ⊗ᴵ Honᴵ)) → Dₚ _
  onR (waitᴿ m)        (inj₁ (queryᴬ x))  = returnₚ (inj₁ ((relayᴿ m , s≤s z≤n) , hashᴿ x))
  onR (waitᴿ nothing)  (inj₁ (commitᴬ c)) =
    returnₚ (inj₂ ((waitᴿ (just c) , z≤n) , inj₂ rcptᴴ))
  onR (waitᴿ (just c)) (inj₁ (openᴬ b r)) =
    returnₚ (inj₁ ((checkᴿ c b , s≤s z≤n) , hashᴿ (b ∷ᵛ r)))
  onR (waitᴿ (just _)) (inj₁ (commitᴬ _)) = botₚ
  onR (waitᴿ nothing)  (inj₁ (openᴬ _ _)) = botₚ
  onR (relayᴿ _)       (inj₁ _)           = botₚ
  onR (checkᴿ _ _)     (inj₁ _)           = botₚ
  onR _                (inj₂ ())

  cohL : (s : RSt) (a : Pos Resᴵ) → mapₚ forget (onL s a) ≈ₚ realStep (s , inj₁ a)
  cohL _            rcptᴿ    = bot-bind-≈ₚ _
  cohL _            (outᴿ _) = bot-bind-≈ₚ _
  cohL _            rejᴿ     = bot-bind-≈ₚ _
  cohL (relayᴿ _)   (digᴿ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (checkᴿ _ _) (digᴿ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (waitᴿ _)    (digᴿ _) = bot-bind-≈ₚ _

  cohR : (s : RSt) (b : Neg (Advᴵ ⊗ᴵ Honᴵ)) → mapₚ forget (onR s b) ≈ₚ realStep (s , inj₂ b)
  cohR (waitᴿ _)        (inj₁ (queryᴬ _))  = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (waitᴿ nothing)  (inj₁ (commitᴬ _)) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (waitᴿ (just _)) (inj₁ (openᴬ _ _)) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (waitᴿ (just _)) (inj₁ (commitᴬ _)) = bot-bind-≈ₚ _
  cohR (waitᴿ nothing)  (inj₁ (openᴬ _ _)) = bot-bind-≈ₚ _
  cohR (relayᴿ _)       (inj₁ (queryᴬ _))  = bot-bind-≈ₚ _
  cohR (relayᴿ _)       (inj₁ (commitᴬ _)) = bot-bind-≈ₚ _
  cohR (relayᴿ _)       (inj₁ (openᴬ _ _)) = bot-bind-≈ₚ _
  cohR (checkᴿ _ _)     (inj₁ (queryᴬ _))  = bot-bind-≈ₚ _
  cohR (checkᴿ _ _)     (inj₁ (commitᴬ _)) = bot-bind-≈ₚ _
  cohR (checkᴿ _ _)     (inj₁ (openᴬ _ _)) = bot-bind-≈ₚ _
  cohR _                (inj₂ ())

recvQB : QB 1 (gradedᵒ real)
recvQB = qb-gradedᵒ (certified⇒QB recvCert)
