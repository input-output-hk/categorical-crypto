{-# OPTIONS --safe --without-K --guardedness #-}

-- The coin-toss stage at the UC model, and its query certificate for
-- `UC-composeᵉ`: the stage makes no downward call at all (`tossCert`), since
-- `Neg Honᴵ` is empty; the receiver's is `Examples.ROCommitment.UC.recvCert`.  The grading's rates are
-- positive, so the stage enters it at `1⁺`.

open import Categories.LocallyGraded.SubCategory


open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Sum.Base
open import Function.Base

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Model.Dominated
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.Examples.CoinToss.UC (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss k
open import CategoricalCrypto.Examples.ROCommitment k

open GradedSubCat gradingᵒ using (Pred)

tossᵒ : ifaceᵒ Honᴵ ⇒ T₀ (ifaceᵒ Advᴵᶜ) (ifaceᵒ Honᴵᶜ)
tossᵒ = gradedᵒ toss

------------------------------------------------------------------------
-- The coin-toss stage spends nothing

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
  onL _ _                     = botₚ

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

tossQB : Pred 1⁺ tossᵒ
tossQB = qb-gradedᵒ (qb-mono z≤n (certified⇒QB tossCert))
